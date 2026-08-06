using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record AtomizerMapping(string Token, string Value);

internal sealed class TheoryAtomizerRules
{
    internal static readonly ImmutableHashSet<string> AllowedKinds = ImmutableHashSet.Create(
        StringComparer.Ordinal, "theorem", "definition", "proposition", "lemma", "corollary",
        "observation", "survey", "note", "remark", "ledger", "entry", "axiom", "example",
        "criterion", "consequence", "principle", "specification", "contract", "theorem-form",
        "frontier-note", "extension-table", "route");

    internal TheoryAtomizerRules(
        ImmutableArray<AtomizerMapping> observerClaimPrefixes,
        ImmutableArray<AtomizerMapping> coneClaimPrefixes,
        ImmutableArray<AtomizerMapping> gictGenres,
        ImmutableArray<AtomizerMapping> gictClaimPrefixes,
        ImmutableArray<AtomizerMapping> gictConstants,
        ImmutableArray<AtomizerMapping> pzgGenres,
        ImmutableDictionary<string, string> pzgMarkers,
        ImmutableArray<AtomizerMapping> pzgHeadingPrefixes,
        ImmutableDictionary<string, string> wmHeadings)
    {
        ObserverClaimPrefixes = observerClaimPrefixes;
        ConeClaimPrefixes = coneClaimPrefixes;
        GictGenres = gictGenres;
        GictClaimPrefixes = gictClaimPrefixes;
        GictConstants = gictConstants;
        PzgGenres = pzgGenres;
        PzgMarkers = pzgMarkers;
        PzgHeadingPrefixes = pzgHeadingPrefixes;
        WmHeadings = wmHeadings;
    }

    internal ImmutableArray<AtomizerMapping> ObserverClaimPrefixes { get; }
    internal ImmutableArray<AtomizerMapping> ConeClaimPrefixes { get; }
    internal ImmutableArray<AtomizerMapping> GictGenres { get; }
    internal ImmutableArray<AtomizerMapping> GictClaimPrefixes { get; }
    internal ImmutableArray<AtomizerMapping> GictConstants { get; }
    internal ImmutableArray<AtomizerMapping> PzgGenres { get; }
    internal ImmutableDictionary<string, string> PzgMarkers { get; }
    internal ImmutableArray<AtomizerMapping> PzgHeadingPrefixes { get; }
    internal ImmutableDictionary<string, string> WmHeadings { get; }
}

internal static class TheoryAtomizerDataLoader
{
    internal const string DataPath = "Meta/Digestion/atomizers.toml";
    internal static ImmutableArray<string> InputPaths { get; } = [DataPath];
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly Regex LocatorPattern = new(
        "^[A-Za-z0-9][A-Za-z0-9.-]*(?:/[A-Za-z0-9][A-Za-z0-9.-]*)+$",
        RegexOptions.CultureInvariant);
    private static readonly Regex ConeLocatorTemplatePattern = new(
        "^(?<kind>[a-z-]+)/\\{number\\}(?:\\|(?<fallback>[a-z-]+)/\\{number\\})?$",
        RegexOptions.CultureInvariant);
    private static readonly string[] SectionOrder =
    [
        "observer.claim_prefixes", "cone.claim_prefixes", "gict.genres",
        "gict.claim_prefixes", "gict.constants", "pzg.genres", "pzg.markers",
        "pzg.heading_prefixes", "wm.headings",
    ];

    internal static TheoryAtomizerRules Load(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        return TryLoad(snapshot, out var rules)
            ? rules
            : throw new FormatException($"Atomizer data file is missing: {DataPath}");
    }

    /// Loads the rules, reporting an ABSENT data file as false rather than throwing.
    ///
    /// Only absence is tolerated, and only so a harness that carries this loader can judge a tree
    /// that predates it: the baseline tree has no atomizers.toml at all, and treating that as a
    /// defect would make the candidate reject a tree the baseline admits, breaking conservative
    /// extension. A data file that IS present stays fully fail-closed -- malformed content still
    /// throws, so nothing can be laundered through this path by corrupting the file. The same
    /// distinction ScribeEmitter draws for not-yet-materialized documents.
    internal static bool TryLoad(RepositorySnapshot snapshot, out TheoryAtomizerRules rules)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        if (!snapshot.TryGetFile(DataPath, out var file))
        {
            rules = null!;
            return false;
        }

        rules = Parse(file);
        return true;
    }

    private static TheoryAtomizerRules Parse(RepositoryFile file)
    {

        string text;
        try
        {
            text = StrictUtf8.GetString(file.RawBytes.AsSpan());
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("Atomizer data is not strict UTF-8.", exception);
        }

        if (text.StartsWith('\uFEFF') || text.Contains('\r'))
        {
            throw new FormatException("Atomizer data must be BOM-free UTF-8 with LF line endings.");
        }

        var entries = SectionOrder.ToDictionary(
            static section => section,
            static _ => new List<Dictionary<string, string>>(),
            StringComparer.Ordinal);
        Dictionary<string, string>? current = null;
        var sectionIndex = -1;
        var sawSchema = false;
        foreach (var rawLine in text.Split('\n'))
        {
            var line = rawLine.Trim();
            if (line.Length == 0 || line.StartsWith('#'))
            {
                continue;
            }

            if (line.StartsWith("[[", StringComparison.Ordinal) && line.EndsWith("]]", StringComparison.Ordinal))
            {
                var section = line[2..^2];
                var index = Array.IndexOf(SectionOrder, section);
                if (index < 0)
                {
                    throw new FormatException($"Unknown atomizer data section '{section}'.");
                }
                if (index < sectionIndex)
                {
                    throw new FormatException("Atomizer data sections are not in canonical order.");
                }
                sectionIndex = index;
                current = new Dictionary<string, string>(StringComparer.Ordinal);
                entries[section].Add(current);
                continue;
            }

            var equals = line.IndexOf(" = ", StringComparison.Ordinal);
            if (equals <= 0)
            {
                throw new FormatException($"Invalid atomizer data line '{line}'.");
            }
            var key = line[..equals];
            var encoded = line[(equals + 3)..];
            if (current is null)
            {
                if (sawSchema || key != "schema_version" || encoded != "1")
                {
                    throw new FormatException("Atomizer data root must contain exactly schema_version = 1.");
                }
                sawSchema = true;
                continue;
            }
            if (encoded.Length < 2 || encoded[0] != '"' || encoded[^1] != '"')
            {
                throw new FormatException($"Atomizer field '{key}' must be a string.");
            }
            var value = Unescape(encoded[1..^1]);
            if (value.Length == 0 || !current.TryAdd(key, value))
            {
                throw new FormatException($"Atomizer field '{key}' is empty or duplicated.");
            }
        }

        if (!sawSchema || entries.Any(static pair =>
                pair.Key != "cone.claim_prefixes" && pair.Value.Count == 0))
        {
            throw new FormatException("Atomizer data is missing schema_version or a required section.");
        }

        var observer = ParseMappings(
            entries["observer.claim_prefixes"],
            "prefix",
            "locator",
            locator: true,
            ordered: true,
            allowAlias: true);
        RejectOverlappingObserverPrefixes(observer);
        var coneClaims = ParseMappings(
            entries["cone.claim_prefixes"],
            "prefix",
            "locator",
            ordered: true);
        ValidateConeClaims(coneClaims);
        var gictGenres = ParseMappings(entries["gict.genres"], "token", "kind", kind: true);
        var gictClaims = ParseMappings(entries["gict.claim_prefixes"], "prefix", "locator", locator: true);
        var gictConstants = ParseMappings(entries["gict.constants"], "name", "locator", locator: true);
        var pzgGenres = ParseMappings(entries["pzg.genres"], "token", "kind", kind: true, longestFirst: true);
        var pzgMarkers = ParseNamedLiterals(entries["pzg.markers"], ["trace-note"]);
        var pzgHeadings = ParseMappings(entries["pzg.heading_prefixes"], "prefix", "locator", locator: true);
        var wm = ParseWm(entries["wm.headings"]);
        return new TheoryAtomizerRules(
            observer, coneClaims, gictGenres, gictClaims, gictConstants,
            pzgGenres, pzgMarkers, pzgHeadings, wm);
    }

    private static void ValidateConeClaims(ImmutableArray<AtomizerMapping> claims)
    {
        var genres = new HashSet<string>(StringComparer.Ordinal);
        foreach (var claim in claims)
        {
            var templates = ConeLocatorTemplatePattern.Match(claim.Value);
            var kinds = templates.Success
                ? new[]
                {
                    templates.Groups["kind"].Value,
                    templates.Groups["fallback"].Value,
                }.Where(static kind => kind.Length > 0)
                : [];
            var formalKind = templates.Success
                && templates.Groups["kind"].Value
                    is "theorem" or "proposition" or "lemma" or "corollary";
            var formalFallback = templates.Success
                && templates.Groups["fallback"].Value
                    is "theorem" or "proposition" or "lemma" or "corollary";
            if (!templates.Success
                || kinds.Any(static kind => !TheoryAtomizerRules.AllowedKinds.Contains(kind))
                || templates.Groups["fallback"].Success != formalKind
                || formalFallback
                || claim.Token.Split('|').Any(genre =>
                    genre.Length == 0
                    || genre.Any(static character => !char.IsLetter(character))
                    || !genres.Add(genre)))
            {
                throw new FormatException("Cone claim prefix or locator template is invalid or duplicated.");
            }
        }
    }

    private static ImmutableArray<AtomizerMapping> ParseMappings(
        List<Dictionary<string, string>> rows,
        string keyName,
        string valueName,
        bool locator = false,
        bool kind = false,
        bool ordered = false,
        bool longestFirst = false,
        bool allowAlias = false)
    {
        var result = ImmutableArray.CreateBuilder<AtomizerMapping>();
        var keys = new HashSet<string>(StringComparer.Ordinal);
        var values = new HashSet<string>(StringComparer.Ordinal);
        foreach (var row in rows)
        {
            var isAlias = allowAlias && row.GetValueOrDefault("alias") == "true";
            if (isAlias)
            {
                RequireFields(row, keyName, valueName, "alias");
            }
            else
            {
                RequireFields(row, keyName, valueName);
            }
            var key = row[keyName];
            var value = row[valueName];
            var firstValue = values.Add(value);
            if (!keys.Add(key) || locator && !firstValue && !isAlias || isAlias && firstValue
                || locator && !LocatorPattern.IsMatch(value)
                || kind && !TheoryAtomizerRules.AllowedKinds.Contains(value))
            {
                throw new FormatException($"Invalid or duplicate mapping in {keyName}/{valueName}.");
            }
            result.Add(new AtomizerMapping(key, value));
        }
        if (!ordered)
        {
            var canonical = longestFirst
                ? result.OrderByDescending(static item => item.Token.Length).ThenBy(static item => item.Token, StringComparer.Ordinal)
                : result.OrderBy(static item => item.Token, StringComparer.Ordinal);
            if (!result.SequenceEqual(canonical))
            {
                throw new FormatException($"Entries for {keyName}/{valueName} are not canonical.");
            }
        }
        return result.ToImmutable();
    }

    private static ImmutableDictionary<string, string> ParseWm(List<Dictionary<string, string>> rows)
    {
        var builder = ImmutableDictionary.CreateBuilder<string, string>(StringComparer.Ordinal);
        foreach (var row in rows)
        {
            RequireFields(row, "role", "text");
            if (row["role"] is not ("title" or "appendix" or "audit") || !builder.TryAdd(row["role"], row["text"]))
            {
                throw new FormatException("WM headings require unique title, appendix, and audit roles.");
            }
        }
        if (!builder.Keys.Order(StringComparer.Ordinal).SequenceEqual(["appendix", "audit", "title"]))
        {
            throw new FormatException("WM headings require title, appendix, and audit roles.");
        }
        return builder.ToImmutable();
    }

    private static ImmutableDictionary<string, string> ParseNamedLiterals(
        List<Dictionary<string, string>> rows,
        string[] roles)
    {
        var builder = ImmutableDictionary.CreateBuilder<string, string>(StringComparer.Ordinal);
        foreach (var row in rows)
        {
            RequireFields(row, "role", "text");
            if (!roles.Contains(row["role"], StringComparer.Ordinal)
                || !builder.TryAdd(row["role"], row["text"]))
            {
                throw new FormatException("Atomizer named literals have unknown or duplicate roles.");
            }
        }
        if (!builder.Keys.Order(StringComparer.Ordinal).SequenceEqual(roles.Order(StringComparer.Ordinal)))
        {
            throw new FormatException("Atomizer named literals omit a required role.");
        }
        return builder.ToImmutable();
    }

    private static void RequireFields(Dictionary<string, string> row, params string[] names)
    {
        if (!row.Keys.Order(StringComparer.Ordinal).SequenceEqual(names.Order(StringComparer.Ordinal), StringComparer.Ordinal))
        {
            throw new FormatException("Atomizer entry has missing or unknown fields.");
        }
    }

    private static void RejectOverlappingObserverPrefixes(ImmutableArray<AtomizerMapping> entries)
    {
        for (var left = 0; left < entries.Length; left++)
        for (var right = left + 1; right < entries.Length; right++)
        {
            if (entries[left].Token.StartsWith(entries[right].Token, StringComparison.Ordinal)
                || entries[right].Token.StartsWith(entries[left].Token, StringComparison.Ordinal))
            {
                throw new FormatException("Observer claim prefixes overlap and make first-match ambiguous.");
            }
        }
    }

    private static string Unescape(string value)
    {
        var builder = new StringBuilder(value.Length);
        for (var index = 0; index < value.Length; index++)
        {
            if (value[index] != '\\') { builder.Append(value[index]); continue; }
            if (++index >= value.Length) throw new FormatException("Invalid TOML string escape.");
            builder.Append(value[index] switch { '\\' => '\\', '"' => '"', 'n' => '\n', 't' => '\t', _ => throw new FormatException("Unsupported TOML string escape.") });
        }
        return builder.ToString();
    }
}

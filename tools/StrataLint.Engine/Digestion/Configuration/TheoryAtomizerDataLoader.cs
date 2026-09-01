using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record AtomizerMapping(string Token, string Value);

/// <summary>
/// A dialect declared entirely in data: one claim pattern plus the genres it may name.
/// A volume in a new shape is digested by adding one of these, not by writing an atomizer.
/// <see cref="HeadingClaims"/> selects which block kind carries the claims: a volume
/// states them either as paragraph leads or as headings, never mixed, so the target is a
/// property of the dialect rather than of the pattern.
/// </summary>
internal sealed record DeclaredDialect(
    string Id,
    string ClaimPattern,
    ImmutableArray<AtomizerMapping> Genres,
    ImmutableArray<AtomizerMapping> GenreSuffixes,
    bool HeadingClaims);

internal static class GenreSuffixResolver
{
    internal static ImmutableArray<AtomizerMapping> Order(IEnumerable<AtomizerMapping> suffixes) =>
        suffixes.OrderByDescending(static item => item.Token.Length)
            .ThenBy(static item => item.Token, StringComparer.Ordinal)
            .ToImmutableArray();

    internal static AtomizerMapping? Resolve(
        string token,
        ImmutableArray<AtomizerMapping> orderedSuffixes) =>
        orderedSuffixes.FirstOrDefault(suffix =>
            token.Length > suffix.Token.Length
            && token.EndsWith(suffix.Token, StringComparison.Ordinal));
}

internal sealed class TheoryAtomizerRules
{
    internal static readonly ImmutableHashSet<string> AllowedKinds = ImmutableHashSet.Create(
        StringComparer.Ordinal, "theorem", "definition", "proposition", "lemma", "corollary",
        "observation", "survey", "note", "remark", "ledger", "entry", "axiom", "example",
        "criterion", "consequence", "principle", "specification", "contract", "theorem-form",
        "frontier-note", "extension-table", "route", "algorithm");

    internal TheoryAtomizerRules(
        ImmutableArray<AtomizerMapping> observerClaimPrefixes,
        ImmutableArray<AtomizerMapping> coneClaimPrefixes,
        ImmutableArray<AtomizerMapping> gictGenres,
        ImmutableArray<AtomizerMapping> gictClaimPrefixes,
        ImmutableArray<AtomizerMapping> gictConstants,
        ImmutableArray<AtomizerMapping> pzgGenres,
        ImmutableDictionary<string, string> pzgMarkers,
        ImmutableArray<AtomizerMapping> pzgHeadingPrefixes,
        ImmutableDictionary<string, string> wmHeadings,
        ImmutableDictionary<string, DeclaredDialect> dialects)
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
        Dialects = dialects;
    }

    /// <summary>
    /// No declared vocabulary at all. The default atomizer reads its locators out of the
    /// source bytes, so it is the one atomizer that can be handed this and still work; any
    /// other atomizer handed this fails closed on its own missing table, which is correct.
    /// </summary>
    internal static TheoryAtomizerRules None { get; } = new(
        [], [], [], [], [], [],
        ImmutableDictionary<string, string>.Empty,
        [],
        ImmutableDictionary<string, string>.Empty,
        ImmutableDictionary<string, DeclaredDialect>.Empty);

    internal ImmutableDictionary<string, DeclaredDialect> Dialects { get; }
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
        "pzg.heading_prefixes", "wm.headings", "dialect", "dialect.genre",
        "dialect.genre_suffix",
    ];

    /// <summary>
    /// Sections a valid file may leave empty. Dialects are declared per volume, so a
    /// repository that has not needed one yet is not thereby malformed.
    /// </summary>
    private static readonly ImmutableHashSet<string> OptionalSections = ImmutableHashSet.Create(
        StringComparer.Ordinal, "cone.claim_prefixes", "dialect", "dialect.genre",
        "dialect.genre_suffix");

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
                !OptionalSections.Contains(pair.Key) && pair.Value.Count == 0))
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
        var dialects = ParseDialects(
            entries["dialect"],
            entries["dialect.genre"],
            entries["dialect.genre_suffix"]);
        return new TheoryAtomizerRules(
            observer, coneClaims, gictGenres, gictClaims, gictConstants,
            pzgGenres, pzgMarkers, pzgHeadings, wm, dialects);
    }

    /// <summary>
    /// Assembles dialects declared in data. Everything is checked here rather than at use:
    /// an uncompilable pattern, an unaccepted kind, a duplicate id or a genre bound to no
    /// declared dialect all refuse the file, so a volume never reaches atomization on a
    /// dialect that cannot work.
    /// </summary>
    private static ImmutableDictionary<string, DeclaredDialect> ParseDialects(
        List<Dictionary<string, string>> declarations,
        List<Dictionary<string, string>> genreRows,
        List<Dictionary<string, string>> genreSuffixRows)
    {
        var genresById = new Dictionary<string, ImmutableArray<AtomizerMapping>.Builder>(
            StringComparer.Ordinal);
        var genreSuffixesById = new Dictionary<string, ImmutableArray<AtomizerMapping>.Builder>(
            StringComparer.Ordinal);
        var ids = new HashSet<string>(StringComparer.Ordinal);
        var builder = ImmutableDictionary.CreateBuilder<string, DeclaredDialect>(StringComparer.Ordinal);
        foreach (var row in declarations)
        {
            var target = row.GetValueOrDefault("target");
            if (target is not null)
            {
                RequireFields(row, "id", "claim", "target");
                if (target != "heading")
                {
                    // The target alphabet is closed: the only declared alternative to the
                    // paragraph default is heading claims, and an unknown value must not
                    // silently fall back to either.
                    throw new FormatException(
                        $"Dialect '{row.GetValueOrDefault("id")}' names unknown claim target '{target}'. "
                        + "Accepted targets: heading.");
                }
            }
            else
            {
                RequireFields(row, "id", "claim");
            }

            if (!ids.Add(row["id"]))
            {
                throw new FormatException($"Duplicate dialect id '{row["id"]}'.");
            }

            try
            {
                _ = new Regex(row["claim"], RegexOptions.CultureInvariant);
            }
            catch (ArgumentException exception)
            {
                throw new FormatException(
                    $"Dialect '{row["id"]}' claim pattern does not compile: {exception.Message}");
            }

            genresById[row["id"]] = ImmutableArray.CreateBuilder<AtomizerMapping>();
            genreSuffixesById[row["id"]] = ImmutableArray.CreateBuilder<AtomizerMapping>();
        }

        foreach (var row in genreRows)
        {
            RequireFields(row, "dialect", "token", "kind");
            if (!genresById.TryGetValue(row["dialect"], out var genres))
            {
                throw new FormatException(
                    $"Genre '{row["token"]}' names dialect '{row["dialect"]}', which is not declared. "
                    + "Declared dialects: "
                    + (ids.Count == 0 ? "(none)" : string.Join(", ", ids.Order(StringComparer.Ordinal)))
                    + ".");
            }

            if (!TheoryAtomizerRules.AllowedKinds.Contains(row["kind"]))
            {
                throw new FormatException(
                    $"Unknown kind '{row["kind"]}' for dialect '{row["dialect"]}' genre '{row["token"]}'. "
                    + "Accepted kinds: "
                    + string.Join(", ", TheoryAtomizerRules.AllowedKinds.Order(StringComparer.Ordinal))
                    + ".");
            }

            if (genres.Any(item => item.Token == row["token"]))
            {
                throw new FormatException(
                    $"Duplicate genre '{row["token"]}' in dialect '{row["dialect"]}'.");
            }

            genres.Add(new AtomizerMapping(row["token"], row["kind"]));
        }

        foreach (var row in genreSuffixRows)
        {
            RequireFields(row, "dialect", "suffix");
            var dialectId = row["dialect"];
            var suffix = row["suffix"];
            if (!genreSuffixesById.TryGetValue(dialectId, out var suffixes))
            {
                throw new FormatException(
                    $"Genre suffix '{suffix}' names dialect '{dialectId}', which is not declared. "
                    + "Declared dialects: "
                    + (ids.Count == 0 ? "(none)" : string.Join(", ", ids.Order(StringComparer.Ordinal)))
                    + ".");
            }

            if (suffix.Any(static character => !char.IsLetter(character)))
            {
                throw new FormatException(
                    $"Genre suffix '{suffix}' in dialect '{dialectId}' must contain only letters.");
            }

            if (suffixes.Any(item => item.Token == suffix))
            {
                throw new FormatException(
                    $"Duplicate genre suffix '{suffix}' in dialect '{dialectId}'.");
            }

            var head = genresById[dialectId].FirstOrDefault(item => item.Token == suffix);
            if (head is null)
            {
                throw new FormatException(
                    $"Genre suffix '{suffix}' in dialect '{dialectId}' does not name a bare exact genre "
                    + "in the same dialect.");
            }

            suffixes.Add(new AtomizerMapping(suffix, head.Value));
        }

        var orderedGenreSuffixesById = genreSuffixesById.ToDictionary(
            static pair => pair.Key,
            static pair => GenreSuffixResolver.Order(pair.Value),
            StringComparer.Ordinal);

        foreach (var dialectId in ids)
        {
            foreach (var genre in genresById[dialectId])
            {
                var winningSuffix = GenreSuffixResolver.Resolve(
                    genre.Token,
                    orderedGenreSuffixesById[dialectId]);
                if (winningSuffix is not null && genre.Value == winningSuffix.Value)
                {
                    throw new FormatException(
                        $"Dialect '{dialectId}' has redundant exact genre '{genre.Token}': suffix "
                        + $"'{winningSuffix.Token}' derives the same kind '{genre.Value}'.");
                }
            }
        }

        foreach (var row in declarations)
        {
            // Longest first so a longer token wins over a shorter one that prefixes it,
            // exactly as the built-in dialects resolve their genres.
            var genres = genresById[row["id"]].ToImmutable()
                .OrderByDescending(static item => item.Token.Length)
                .ThenBy(static item => item.Token, StringComparer.Ordinal)
                .ToImmutableArray();
            var genreSuffixes = orderedGenreSuffixesById[row["id"]];
            builder.Add(row["id"], new DeclaredDialect(
                row["id"],
                row["claim"],
                genres,
                genreSuffixes,
                row.GetValueOrDefault("target") == "heading"));
        }

        return builder.ToImmutable();
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
            if (kind && !TheoryAtomizerRules.AllowedKinds.Contains(value))
            {
                // The kind alphabet is closed by design, but naming it here is what turns a
                // rejected registration into a one-step fix instead of a guessing game.
                throw new FormatException(
                    $"Unknown {valueName} '{value}' for {keyName} '{key}'. Accepted {valueName}s: "
                    + string.Join(", ", TheoryAtomizerRules.AllowedKinds.Order(StringComparer.Ordinal))
                    + ".");
            }

            if (!keys.Add(key) || locator && !firstValue && !isAlias || isAlias && firstValue
                || locator && !LocatorPattern.IsMatch(value))
            {
                throw new FormatException($"Invalid or duplicate mapping in {keyName}/{valueName}.");
            }
            result.Add(new AtomizerMapping(key, value));
        }
        if (!ordered)
        {
            // Match order is derived, not a maintenance obligation. Longest-first is what
            // makes a longer token win over a shorter one that prefixes it (注记 over 注);
            // requiring the file to already be in that order only meant that registering a
            // new volume's genres could fail on placement rather than on content.
            return (longestFirst
                ? result.OrderByDescending(static item => item.Token.Length)
                    .ThenBy(static item => item.Token, StringComparer.Ordinal)
                : result.OrderBy(static item => item.Token, StringComparer.Ordinal))
                .ToImmutableArray();
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

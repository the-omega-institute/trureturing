using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe;

internal sealed record LibraryNote(
    BibKey BibKey,
    string Authors,
    int Year,
    string Title,
    Doi? Doi,
    string Claim,
    ImmutableArray<GidRef> StrataTouched,
    string License,
    LibraryTriage Triage,
    string RelativePath);

internal abstract record LibraryTriage
{
    private LibraryTriage() { }

    internal sealed record Anchor : LibraryTriage;

    internal sealed record Task(GidRef Reference) : LibraryTriage;

    internal sealed record Rejected(string Reason) : LibraryTriage;
}

internal sealed record LibraryNoteCatalogFinding(
    string Code,
    string Path,
    string Message);

internal sealed record LibraryNoteCatalogInspection(
    ImmutableArray<LibraryNote> Notes,
    ImmutableArray<LibraryNoteCatalogFinding> Findings);

internal sealed class LibraryNoteCatalog
{
    private const string LibraryRoot = "Library/";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly HashSet<string> RequiredKeys =
    [
        "bibkey",
        "authors",
        "year",
        "title",
        "doi",
        "claim",
        "strata_touched",
        "license",
        "triage",
    ];

    private LibraryNoteCatalog(ImmutableArray<LibraryNote> notes) => Notes = notes;

    internal ImmutableArray<LibraryNote> Notes { get; }

    internal IReadOnlyDictionary<string, LiteratureCitation> Citations =>
        Notes.ToDictionary(
            static note => note.BibKey.Value,
            static note => LiteratureCitation.Create(
                note.Authors,
                note.Year,
                note.Title,
                note.Doi?.Value
                    ?? throw new FormatException(
                        $"{note.RelativePath} requires a DOI for academic citation")),
            StringComparer.Ordinal);

    internal static LibraryNoteCatalog Load(string repositoryRoot)
    {
        var inspection = Inspect(repositoryRoot);
        if (!inspection.Findings.IsEmpty)
        {
            throw new FormatException(string.Join(
                "; ",
                inspection.Findings.Select(static finding => finding.Message)));
        }

        return new LibraryNoteCatalog(inspection.Notes);
    }

    internal static LibraryNoteCatalogInspection Inspect(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var directory = Path.Combine(repositoryRoot, "Library");
        if (!Directory.Exists(directory))
        {
            return new LibraryNoteCatalogInspection([], []);
        }

        var notes = ImmutableArray.CreateBuilder<LibraryNote>();
        var findings = ImmutableArray.CreateBuilder<LibraryNoteCatalogFinding>();
        foreach (var path in Directory.EnumerateDirectories(directory)
                     .SelectMany(static bucket =>
                         Directory.EnumerateFiles(bucket, "*.md", SearchOption.TopDirectoryOnly))
                     .Order(StringComparer.Ordinal))
        {
            try
            {
                notes.Add(Parse(repositoryRoot, path));
            }
            catch (Exception exception) when (exception is FormatException or ArgumentException)
            {
                var relativePath = RelativePath(repositoryRoot, path);
                findings.Add(new LibraryNoteCatalogFinding(
                    exception.Message.Contains("DOI", StringComparison.OrdinalIgnoreCase)
                        ? "invalid-doi"
                        : "invalid-library-note",
                    relativePath,
                    exception.Message));
            }
        }

        var bibkeys = new Dictionary<string, string>(StringComparer.Ordinal);
        var dois = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
        foreach (var note in notes)
        {
            if (!bibkeys.TryAdd(note.BibKey.Value, note.RelativePath))
            {
                findings.Add(new LibraryNoteCatalogFinding(
                    "duplicate-bibkey",
                    note.RelativePath,
                    $"duplicate bibkey {note.BibKey.Value} in "
                    + $"{bibkeys[note.BibKey.Value]} and {note.RelativePath}"));
            }

            if (note.Doi is not null && !dois.TryAdd(note.Doi.Value, note.RelativePath))
            {
                findings.Add(new LibraryNoteCatalogFinding(
                    "duplicate-doi",
                    note.RelativePath,
                    $"duplicate DOI {note.Doi.Value} in {dois[note.Doi.Value]} and {note.RelativePath}"));
            }
        }

        return new LibraryNoteCatalogInspection(
            notes.ToImmutable(),
            findings
                .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
                .ThenBy(static finding => finding.Code, StringComparer.Ordinal)
                .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
                .ToImmutableArray());
    }

    internal static bool IsVerificationInput(RepoPath path) =>
        path.Value.StartsWith(LibraryRoot, StringComparison.Ordinal);

    private static LibraryNote Parse(string repositoryRoot, string path)
    {
        string text;
        try
        {
            text = StrictUtf8.GetString(File.ReadAllBytes(path));
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("Library note must be strict UTF-8.", exception);
        }

        var relativePath = RelativePath(repositoryRoot, path);
        if (text.StartsWith('\uFEFF') || text.Contains('\r'))
        {
            throw new FormatException($"{relativePath} must be UTF-8 without BOM or CR characters");
        }

        const string opening = "---\n";
        const string closing = "\n---\n";
        if (!text.StartsWith(opening, StringComparison.Ordinal))
        {
            throw new FormatException($"{relativePath} needs canonical YAML front matter");
        }

        var end = text.IndexOf(closing, opening.Length, StringComparison.Ordinal);
        if (end < 0)
        {
            throw new FormatException($"{relativePath} has unterminated YAML front matter");
        }

        var metadata = (Dictionary<string, object?>)YamlSubsetParser.Parse(
            text[opening.Length..end]);
        if (!metadata.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(RequiredKeys))
        {
            throw new FormatException($"{relativePath} has missing or unknown metadata fields");
        }

        var rawBibKey = RequiredString(metadata, "bibkey", relativePath);
        var bibKey = BibKey.TryCreate(rawBibKey)
            ?? throw new FormatException($"{relativePath} has a noncanonical bibkey");
        var pathBibKey = Path.GetFileNameWithoutExtension(path);
        if (!string.Equals(bibKey.Value, pathBibKey, StringComparison.Ordinal))
        {
            throw new FormatException($"{relativePath} bibkey disagrees with its path");
        }

        var title = RequiredLine(metadata, "title", relativePath);
        var authors = RequiredLine(metadata, "authors", relativePath);
        var year = metadata["year"] is int rawYear && rawYear is >= 1000 and <= 9999
            ? rawYear
            : throw new FormatException($"{relativePath} field year must be a four-digit integer");
        var claim = RequiredLine(metadata, "claim", relativePath);
        var license = RequiredLine(metadata, "license", relativePath);
        var triage = ParseTriage(RequiredLine(metadata, "triage", relativePath), relativePath);

        Doi? doi = metadata["doi"] switch
        {
            null => null,
            string value when Doi.TryCreate(value, out var parsed) => parsed,
            _ => throw new FormatException($"{relativePath} has a malformed DOI"),
        };
        if (metadata["strata_touched"] is not List<object?> rawStrata)
        {
            throw new FormatException($"{relativePath} strata_touched must be a list");
        }

        var strata = rawStrata.Select((value, index) => value is string gid
                ? GidRef.Create(gid)
                : throw new FormatException(
                    $"{relativePath} strata_touched item {index} must be a GID"))
            .ToImmutableArray();
        return new LibraryNote(
            bibKey,
            authors,
            year,
            title,
            doi,
            claim,
            strata,
            license,
            triage,
            relativePath);
    }

    private static LibraryTriage ParseTriage(string value, string path)
    {
        if (value == "anchor")
        {
            return new LibraryTriage.Anchor();
        }

        if (value.StartsWith("task(", StringComparison.Ordinal) && value.EndsWith(')'))
        {
            var rawGid = value["task(".Length..^1];
            try
            {
                return new LibraryTriage.Task(GidRef.Create(rawGid));
            }
            catch (ArgumentException exception)
            {
                throw new FormatException($"{path} has a noncanonical task triage GID", exception);
            }
        }

        if (value.StartsWith("rejected(", StringComparison.Ordinal) && value.EndsWith(')'))
        {
            var reason = value["rejected(".Length..^1];
            if (!string.IsNullOrWhiteSpace(reason)
                && string.Equals(reason, reason.Trim(), StringComparison.Ordinal))
            {
                return new LibraryTriage.Rejected(reason);
            }
        }

        throw new FormatException($"{path} has a noncanonical triage value");
    }

    private static string RequiredString(
        IReadOnlyDictionary<string, object?> metadata,
        string key,
        string path) => metadata[key] is string value
            ? value
            : throw new FormatException($"{path} field {key} must be a string");

    private static string RequiredLine(
        IReadOnlyDictionary<string, object?> metadata,
        string key,
        string path)
    {
        var value = RequiredString(metadata, key, path);
        if (string.IsNullOrWhiteSpace(value)
            || !string.Equals(value, value.Trim(), StringComparison.Ordinal)
            || value.IndexOfAny(['\r', '\n']) >= 0)
        {
            throw new FormatException($"{path} field {key} must be one canonical non-empty line");
        }

        return value;
    }

    private static string RelativePath(string repositoryRoot, string path) =>
        Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/');
}

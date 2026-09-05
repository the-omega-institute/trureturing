using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe;

internal enum ProblemTriage
{
    Theorem,
    Window,
    Wall,
}

internal sealed record ProblemCandidate(
    string Slug,
    BibKey BibKey,
    string ArxivId,
    ProblemTriage Triage,
    ImmutableArray<GidRef> MotivationGids,
    string RelativePath);

internal sealed record ProblemCandidateFinding(
    string Code,
    string Path,
    string Message);

internal sealed record ProblemCandidateCatalogInspection(
    ImmutableArray<ProblemCandidate> Candidates,
    ImmutableArray<ProblemCandidateFinding> Findings);

/// <summary>
/// Loads the literature-sourced open problem pool defined by spec 11.20.3. Every
/// tracked file under <c>Problems/</c> must be one candidate dossier; a file that
/// is not one — an index, a summary, any aggregate — fails to parse and is
/// reported, which is how the one-problem-one-file partition is enforced.
/// </summary>
internal sealed class ProblemCandidateCatalog
{
    private const string FrozenStateRoot = "Golden/Frozen/state/";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly HashSet<string> RequiredKeys =
    [
        "slug",
        "bibkey",
        "arxiv_id",
        "triage",
        "motivation_gids",
    ];

    // The section set is closed and mirrors the six Theorist charter outputs
    // (motivation, exact statement, falsifier, evidence, source search, triage)
    // plus the gap and route a not-yet-stated problem still owes its reader.
    private static readonly ImmutableArray<string> RequiredSections =
    [
        "Problem",
        "Motivation",
        "Gap",
        "Route",
        "Falsifier",
        "Evidence",
        "Triage",
        "ASSUMED-UNVERIFIED",
    ];

    // arXiv identifiers are the bare YYMM.NNNNN form. A version suffix is
    // deliberately rejected: the note owns the version-specific locator, and two
    // spellings of one paper would be two addresses for one thing.
    private static readonly Regex ArxivIdPattern = new(
        "^[0-9]{4}\\.[0-9]{4,5}$",
        RegexOptions.CultureInvariant);

    private ProblemCandidateCatalog(ImmutableArray<ProblemCandidate> candidates) =>
        Candidates = candidates;

    internal ImmutableArray<ProblemCandidate> Candidates { get; }

    internal static ProblemCandidateCatalog Load(string repositoryRoot)
    {
        var inspection = Inspect(repositoryRoot);
        if (!inspection.Findings.IsEmpty)
        {
            throw new FormatException(string.Join(
                "; ",
                inspection.Findings.Select(static finding => finding.Message)));
        }

        return new ProblemCandidateCatalog(inspection.Candidates);
    }

    internal static ProblemCandidateCatalogInspection Inspect(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var directory = Path.Combine(repositoryRoot, ProblemPoolPaths.DirectoryName);
        if (!Directory.Exists(directory))
        {
            return new ProblemCandidateCatalogInspection([], []);
        }

        var candidates = ImmutableArray.CreateBuilder<ProblemCandidate>();
        var findings = ImmutableArray.CreateBuilder<ProblemCandidateFinding>();
        foreach (var path in Directory
                     .EnumerateFiles(directory, "*.md", SearchOption.TopDirectoryOnly)
                     .Order(StringComparer.Ordinal))
        {
            try
            {
                candidates.Add(Parse(repositoryRoot, path));
            }
            catch (Exception exception) when (exception is FormatException or ArgumentException)
            {
                findings.Add(new ProblemCandidateFinding(
                    "invalid-problem-candidate",
                    RelativePath(repositoryRoot, path),
                    exception.Message));
            }
        }

        return new ProblemCandidateCatalogInspection(
            candidates.ToImmutable(),
            findings
                .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
                .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
                .ToImmutableArray());
    }

    internal static Func<RepoPath, bool> VerificationInputPredicate(
        RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var hasProblemDirectory = snapshot.Files.Keys.Any(IsProblemPoolInput);
        return path => IsProblemPoolInput(path)
            || hasProblemDirectory
                && path.Value.StartsWith(FrozenStateRoot, StringComparison.Ordinal);
    }

    private static bool IsProblemPoolInput(RepoPath path) =>
        path.Value.StartsWith(
            ProblemPoolPaths.DirectoryName + "/",
            StringComparison.Ordinal);

    private static ProblemCandidate Parse(string repositoryRoot, string path)
    {
        string text;
        try
        {
            text = StrictUtf8.GetString(File.ReadAllBytes(path));
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("problem candidate must be strict UTF-8.", exception);
        }

        var relativePath = RelativePath(repositoryRoot, path);
        if (text.StartsWith('﻿') || text.Contains('\r'))
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

        var metadata = (Dictionary<string, object?>)YamlSubsetParser.Parse(text[opening.Length..end]);
        if (!metadata.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(RequiredKeys))
        {
            throw new FormatException($"{relativePath} has missing or unknown metadata fields");
        }

        var slug = RequiredLine(metadata, "slug", relativePath);
        if (!ProblemPoolPaths.IsCanonicalSlug(slug))
        {
            throw new FormatException($"{relativePath} has a noncanonical slug");
        }

        if (!string.Equals(slug, Path.GetFileNameWithoutExtension(path), StringComparison.Ordinal))
        {
            throw new FormatException($"{relativePath} slug disagrees with its path");
        }

        var bibKey = BibKey.TryCreate(RequiredLine(metadata, "bibkey", relativePath))
            ?? throw new FormatException($"{relativePath} has a noncanonical bibkey");
        var arxivId = RequiredLine(metadata, "arxiv_id", relativePath);
        if (!ArxivIdPattern.IsMatch(arxivId))
        {
            throw new FormatException($"{relativePath} has a noncanonical arxiv_id");
        }

        var triage = RequiredLine(metadata, "triage", relativePath) switch
        {
            "theorem" => ProblemTriage.Theorem,
            "window" => ProblemTriage.Window,
            "wall" => ProblemTriage.Wall,
            _ => throw new FormatException($"{relativePath} has a noncanonical triage value"),
        };

        if (metadata["motivation_gids"] is not List<object?> rawChain || rawChain.Count == 0)
        {
            throw new FormatException($"{relativePath} motivation_gids must be a nonempty list");
        }

        var motivation = rawChain.Select((value, index) => value is string gid
                ? GidRef.Create(gid)
                : throw new FormatException(
                    $"{relativePath} motivation_gids item {index} must be a GID"))
            .ToImmutableArray();
        var duplicate = motivation
            .GroupBy(static reference => reference.Value, StringComparer.Ordinal)
            .FirstOrDefault(static group => group.Count() > 1);
        if (duplicate is not null)
        {
            throw new FormatException(
                $"{relativePath} lists duplicate motivation GID {duplicate.Key}");
        }

        ValidateSections(text[(end + closing.Length)..], relativePath);
        return new ProblemCandidate(slug, bibKey, arxivId, triage, motivation, relativePath);
    }

    private static void ValidateSections(string body, string relativePath)
    {
        var lines = body.Split('\n');
        var order = new List<string>();
        var contentByHeading = new Dictionary<string, bool>(StringComparer.Ordinal);
        var current = string.Empty;
        foreach (var line in lines)
        {
            if (line.StartsWith("## ", StringComparison.Ordinal))
            {
                current = line["## ".Length..].Trim();
                order.Add(current);
                contentByHeading.TryAdd(current, false);
                continue;
            }

            if (current.Length > 0 && line.Trim().Length > 0)
            {
                contentByHeading[current] = true;
            }
        }

        var unknown = order.FirstOrDefault(heading => !RequiredSections.Contains(heading));
        if (unknown is not null)
        {
            throw new FormatException($"{relativePath} has an unknown section {unknown}");
        }

        foreach (var heading in RequiredSections)
        {
            var occurrences = order.Count(name =>
                string.Equals(name, heading, StringComparison.Ordinal));
            if (occurrences == 0)
            {
                throw new FormatException($"{relativePath} is missing section {heading}");
            }

            if (occurrences > 1)
            {
                throw new FormatException($"{relativePath} repeats section {heading}");
            }

            if (!contentByHeading[heading])
            {
                throw new FormatException($"{relativePath} has an empty section {heading}");
            }
        }
    }

    private static string RequiredLine(
        IReadOnlyDictionary<string, object?> metadata,
        string key,
        string path)
    {
        if (metadata[key] is not string value)
        {
            throw new FormatException($"{path} field {key} must be a string");
        }

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

using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static ImmutableArray<RuleFinding> AddressesAndFormulas(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var evidence = new Dictionary<(string Coordinates, string Selector), List<string>>();
        var seenGids = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        foreach (var (path, file) in context.Current.Files.OrderBy(item => item.Key.Value, StringComparer.Ordinal))
        {
            if (RepositoryPathPolicy.Validate(path, context.Policy) is not null)
            {
                continue;
            }

            if (RepositoryPathPolicy.TryResolve(path, context.Policy, out var gid) && gid is not null)
            {
                var gidText = gid.Value;
                if (gidText.Contains("/E/", StringComparison.Ordinal))
                {
                    var separator = gidText.LastIndexOf("--", StringComparison.Ordinal);
                    var dot = separator < 0 ? -1 : gidText.LastIndexOf('.', separator);
                    if (dot > 0)
                    {
                        var key = (gidText[..dot], gidText[(dot + 1)..separator]);
                        if (!evidence.TryGetValue(key, out var paths))
                        {
                            paths = new List<string>();
                            evidence.Add(key, paths);
                        }

                        paths.Add(path.Value);
                    }
                }
            }

            if (path.Value.EndsWith(".json", StringComparison.Ordinal))
            {
                ValidateFormulas(path.Value, file.Text, findings);
            }

            if (TryHeader(file.Text, out var header))
            {
                if (!SafeFieldPattern.IsMatch(header.Gid))
                {
                    findings.Add(new RuleFinding(path.Value, "GID violates the machine-field character set"));
                }
                else
                {
                    if (!seenGids.TryGetValue(header.Gid, out var gidPaths))
                    {
                        gidPaths = new List<string>();
                        seenGids.Add(header.Gid, gidPaths);
                    }

                    gidPaths.Add(path.Value);
                }

                foreach (var anchor in header.Anchors)
                {
                    if (!Anchor.IsExternalFamily(anchor)
                        || Anchor.TryParseCanonical(anchor) is AnchorParseResult.Invalid)
                    {
                        findings.Add(new RuleFinding(
                            path.Value,
                            $"anchor '{anchor}' is not a canonical external anchor"));
                    }
                }
            }
        }

        foreach (var duplicate in seenGids.Where(static item => item.Value.Count > 1))
        {
            var locations = string.Join(", ", duplicate.Value.Order(StringComparer.Ordinal));
            foreach (var path in duplicate.Value)
            {
                findings.Add(new RuleFinding(
                    path,
                    $"duplicate GID {duplicate.Key} at {locations}"));
            }
        }

        foreach (var collision in evidence.Where(static item => item.Value.Count > 1))
        {
            foreach (var path in collision.Value)
            {
                findings.Add(new RuleFinding(
                    path,
                    "evidence selector has multiple artifact kinds: "
                    + string.Join(", ", collision.Value.Order(StringComparer.Ordinal))));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Literature(RuleEvaluationContext context)
    {
        const string path = "Library/queries.yaml";
        if (!context.Current.TryGetFile(path, out var file))
        {
            return ImmutableArray.Create(new RuleFinding(path, "required governance document is missing"));
        }

        Dictionary<string, object?> root;
        try
        {
            root = (Dictionary<string, object?>)YamlSubsetParser.Parse(file.Text);
        }
        catch (FormatException exception)
        {
            return ImmutableArray.Create(new RuleFinding(path, exception.Message));
        }

        if (!root.TryGetValue("queries", out var rawQueries) || rawQueries is not List<object?> queries)
        {
            return ImmutableArray.Create(new RuleFinding(path, "queries must be a list"));
        }

        var tasks = CollectTaskCodes(context.Current);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var ids = new HashSet<string>(StringComparer.Ordinal);
        foreach (var rawQuery in queries)
        {
            if (rawQuery is not Dictionary<string, object?> query
                || !query.TryGetValue("id", out var rawId)
                || rawId is not string id)
            {
                findings.Add(new RuleFinding(path, "query entry needs an id"));
                continue;
            }

            if (!QueryPattern.IsMatch(id) || !ids.Add(id))
            {
                findings.Add(new RuleFinding(path, $"invalid or duplicate query id {id}"));
            }

            query.TryGetValue("target_gid", out var rawTarget);
            var target = rawTarget as string;
            Gid? targetGid = null;
            if (target is null || !Gid.TryParse(target, out targetGid))
            {
                var reason = target is null
                    ? "target_gid is missing"
                    : target.StartsWith("D5/E/", StringComparison.Ordinal)
                        && !target.Contains("--", StringComparison.Ordinal)
                            ? "Evidence GID needs an explicit supported artifact kind tag"
                            : "target inverse is not an identity";
                findings.Add(new RuleFinding(path, $"query {id} has noncanonical target: {reason}"));
            }

            ValidateQuerySource(context.Current, root, query, id, findings);

            query.TryGetValue("pending_case", out var rawPending);
            if (rawPending is string pending)
            {
                if (!CasePattern.IsMatch(pending) || !tasks.Contains(pending))
                {
                    findings.Add(new RuleFinding(path, $"query {id} has unresolved pending case {pending}"));
                }

                continue;
            }

            if (targetGid is not null && !context.Current.TryGetFile(targetGid.Path.Value, out _))
            {
                findings.Add(new RuleFinding(path, $"query {id} target GID is missing: {targetGid.Value}"));
            }

            var hasIdentifier = query.TryGetValue("doi", out var rawDoi)
                    && rawDoi is string doi
                    && Doi.TryCreate(doi, out _)
                || query.TryGetValue("arxiv", out var rawArxiv)
                    && rawArxiv is string arxiv
                    && ArxivPattern.IsMatch(arxiv);
            if (!hasIdentifier)
            {
                findings.Add(new RuleFinding(path, $"query {id} needs DOI/arXiv or a pending case"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> ResolvableAnchors(RuleEvaluationContext context) =>
        Literature(context).AddRange(AnchorReferenceRule.Evaluate(context));

    private static void ValidateQuerySource(
        RepositorySnapshot snapshot,
        IReadOnlyDictionary<string, object?> root,
        IReadOnlyDictionary<string, object?> query,
        string id,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        // Positional anchors (source_line/fragment_sha256) are retired: position is
        // not identity, git already content-addresses sources, and line anchors
        // shatter on unrelated edits. The fields are IGNORED (not rejected) so no
        // previously admitted artifact flips to rejected (conservative extension:
        // admits are load-bearing, rejects may loosen). A query cites a source by
        // path only; deeper binding belongs to typed references (Scribe).
        if (!query.TryGetValue("source_path", out var rawSourcePath))
        {
            return;
        }

        if (rawSourcePath is not string sourcePath || !RepoPath.TryCreate(sourcePath, out _))
        {
            findings.Add(new RuleFinding("Library/queries.yaml", $"query {id} source path is not workspace-relative"));
            return;
        }

        if (!snapshot.TryGetFile(sourcePath, out _))
        {
            findings.Add(new RuleFinding("Library/queries.yaml", $"query {id} source path is missing: {sourcePath}"));
        }
    }

    private static ImmutableArray<RuleFinding> Values(RuleEvaluationContext context)
    {
        var findings = context.Current.Files.Keys
            .Where(static path =>
                path.Value.StartsWith("Evidence/D5/values.", StringComparison.Ordinal)
                && path.Value != RepositoryPathPolicy.ValuesProjectionPath)
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .Select(static path => new RuleFinding(
                path.Value,
                "canonical values projection must be Evidence/D5/values.json"))
            .ToImmutableArray()
            .ToBuilder();
        if (!context.Current.TryGetFile(ValuesKernelBindingValidator.RelativePath, out var values))
        {
            findings.Add(new RuleFinding(
                ValuesKernelBindingValidator.RelativePath,
                "required values kernel binding data is missing"));
        }
        else
        {
            findings.AddRange(ValuesKernelBindingValidator.Validate(values.Text, context.Lean.Report));
        }

        return findings.ToImmutable();
    }
}

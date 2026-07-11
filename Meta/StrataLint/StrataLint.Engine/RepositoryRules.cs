using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class RepositoryRules
{
    private static readonly Regex HeaderPattern = new(
        "\\A/- GID: (?<gid>[^\\n]+)\\n"
        + "   generality: (?<generality>[GIE])\\n"
        + "   mirror-B: (?<mirrorB>[^\\n]+)\\n"
        + "   mirror-E: (?<mirrorE>[^\\n]+)\\n"
        + "   anchors: \\[(?<anchors>[^\\n]*)\\]\\n"
        + "   digest: (?<digest>[^\\n]+) -/\\n?",
        RegexOptions.CultureInvariant);

    private static readonly Regex BadgePattern = new(
        "(?:status\\s*:\\s*(?:proven|admitted|conditional|open)|"
        + "状态\\s*[:：]\\s*(?:已证|承典|条件|开放)|〔(?:已证|承典|条件|开放)〕)",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly Regex TaskTokenPattern = new(
        "TASK\\s+(D[0-9]+-T[0-9]{4})",
        RegexOptions.CultureInvariant);

    private static readonly Regex TaskPattern = new(
        "/-- TASK (?<code>D5-T[0-9]{4}) \\| 难度:[1-5] \\| 依赖:[^\\n|]+ \\| 尝试:[0-9]+\\n"
        + "\\s+提示:[^\\n]+\\n\\s+尸检:(?<autopsy>[^\\n]+) -/",
        RegexOptions.CultureInvariant);

    private static readonly Regex SafeFieldPattern = new(
        "^[A-Za-z0-9_/.-]+$",
        RegexOptions.CultureInvariant);

    private static readonly Regex CasePattern = new(
        "^D5-T[0-9]{4}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex QueryPattern = new(
        "^D5-Q[0-9]{4}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex DoiPattern = new(
        "^10\\.[0-9]{4,9}/\\S+$",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly Regex ArxivPattern = new(
        "^(?:arXiv:)?[0-9]{4}\\.[0-9]{4,5}(?:v[0-9]+)?$",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly Regex AnomalyKindPattern = new(
        "^(?:[a-z0-9]+-)*(?:anomaly|exception|failure|tension)(?:-[a-z0-9]+)*$",
        RegexOptions.CultureInvariant);

    private static readonly Regex AnomalyBearingPattern = new(
        "anomal|exception|failure|tension",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly Regex Sha256Pattern = new(
        "^[0-9a-f]{64}$",
        RegexOptions.CultureInvariant);

    private static readonly ImmutableHashSet<string> AnomalySchemaKeys =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "anomaly", "anomalies", "case", "case_id", "category", "exception", "exceptions",
            "failure", "failures", "kind", "record_type", "resolution", "state", "tension",
            "tensions", "type", "unresolved");

    internal static ImmutableArray<RuleFinding> Evaluate(int number, RuleEvaluationContext context) =>
        number switch
        {
            1 => Imports(context),
            2 => Sorry(context),
            3 => Capacity(context),
            4 => Mirrors(context),
            5 => Chronicle(context),
            6 => Badges(context),
            7 => ImmutableArray<RuleFinding>.Empty,
            8 => Hearts(context),
            9 => ImmutableArray<RuleFinding>.Empty,
            10 => Generality(context),
            11 => Domains(context),
            12 => Headers(context),
            13 => Tasks(context),
            14 => ImmutableArray<RuleFinding>.Empty,
            15 => AddressesAndFormulas(context),
            16 => BackfillInventoryRule.Evaluate(context),
            17 => Literature(context),
            18 => Values(context),
            19 => Ledger(context),
            20 => Axioms(context),
            21 => Instantiation(context),
            22 => Bootstrap(context),
            _ => throw new InvalidOperationException($"Unknown rule number {number}."),
        };

    private static ImmutableArray<RuleFinding> Imports(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, report) in context.Lean.Report.Files.OrderBy(item => item.Key.Value, StringComparer.Ordinal))
        {
            foreach (var module in report.Imports.Where(static item => item.StartsWith("D5.", StringComparison.Ordinal)))
            {
                var target = module.Replace('.', '/') + ".lean";
                if (!context.Current.TryGetFile(target, out _))
                {
                    findings.Add(new RuleFinding(path.Value, $"managed import {target} does not exist"));
                }
                else if (!ImportAllowed(path.Value, target))
                {
                    findings.Add(new RuleFinding(path.Value, $"stratum closure may not import {target}"));
                }
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Sorry(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, report) in context.Lean.Report.Files)
        {
            var declarations = report.Declarations
                .Where(static item => item.Axioms.Contains("sorryAx", StringComparer.Ordinal))
                .Select(static item => item.Name)
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (declarations.Length > 0 && !path.Value.Contains("/X_Frontier/", StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "sorryAx occurs in declaration closure: " + string.Join(", ", declarations)));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Capacity(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var directories = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var (path, file) in context.Current.Files)
        {
            if (path.Value.StartsWith("docs/develop/", StringComparison.Ordinal)
                || string.Equals(path.Value, "lake-manifest.json", StringComparison.Ordinal))
            {
                continue;
            }

            var lineCount = file.Text.Split('\n').Length - (file.Text.EndsWith('\n') ? 1 : 0);
            if (lineCount > 400)
            {
                findings.Add(new RuleFinding(path.Value, "artifact exceeds 400 lines"));
            }

            var slash = path.Value.LastIndexOf('/');
            var directory = slash < 0 ? "." : path.Value[..slash];
            directories[directory] = directories.GetValueOrDefault(directory) + 1;
        }

        findings.AddRange(directories
            .Where(static item => item.Value > 12)
            .Select(static item => new RuleFinding(
                item.Key,
                $"directory contains {item.Value} files (maximum 12)")));
        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Mirrors(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, file) in FormalFiles(context.Current))
        {
            if (!TryHeader(file.Text, out var header))
            {
                continue;
            }

            ValidateMirror(path.Value, "mirror-B", header.MirrorB, "D5/B/", context.Current, findings);
            ValidateMirror(path.Value, "mirror-E", header.MirrorE, "D5/E/", context.Current, findings);
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Chronicle(RuleEvaluationContext context) =>
        context.Baseline.Files
            .Where(static item => item.Key.Value.StartsWith("Chronicle/", StringComparison.Ordinal))
            .Where(item => !context.Current.TryGetFile(item.Key.Value, out var current)
                || !current.RawBytes.AsSpan().SequenceEqual(item.Value.RawBytes.AsSpan()))
            .Select(static item => new RuleFinding(item.Key.Value, "tracked Chronicle entries are append-only"))
            .ToImmutableArray();

    private static ImmutableArray<RuleFinding> Badges(RuleEvaluationContext context) =>
        context.Current.Files
            .Where(static item => IsStatusScope(item.Key.Value) && BadgePattern.IsMatch(item.Value.Text))
            .Select(static item => new RuleFinding(item.Key.Value, "hand-written status badge is forbidden"))
            .ToImmutableArray();

    private static ImmutableArray<RuleFinding> Hearts(RuleEvaluationContext context)
    {
        const string path = "D5/X_Frontier/Hearts.lean";
        var hadBaseline = context.Baseline.TryGetFile(path, out _);
        var hasCurrent = context.Current.TryGetFile(path, out _);
        if (hadBaseline && !hasCurrent)
        {
            return ImmutableArray.Create(new RuleFinding(path, "frozen Hearts.lean was deleted"));
        }

        if (!hadBaseline && hasCurrent)
        {
            return ImmutableArray.Create(new RuleFinding(path, "new Hearts.lean requires a human-gated baseline"));
        }

        if (!hadBaseline)
        {
            return ImmutableArray<RuleFinding>.Empty;
        }

        if (!RepoPath.TryCreate(path, out var repoPath)
            || !context.BaselineLean.Report.Files.TryGetValue(repoPath, out var baseline)
            || !context.Lean.Report.Files.TryGetValue(repoPath, out var current))
        {
            return ImmutableArray.Create(new RuleFinding(path, "protected Hearts baseline has no semantic report"));
        }

        if (!string.IsNullOrEmpty(baseline.Error))
        {
            return ImmutableArray.Create(new RuleFinding(path, "protected Hearts baseline has no semantic report"));
        }

        if (!string.IsNullOrEmpty(current.Error))
        {
            return ImmutableArray.Create(new RuleFinding(path, $"Hearts semantic report failed: {current.Error}"));
        }

        return CanonicalStatementWriter.WriteModule(repoPath, baseline).AsSpan()
            .SequenceEqual(CanonicalStatementWriter.WriteModule(repoPath, current).AsSpan())
                ? ImmutableArray<RuleFinding>.Empty
                : ImmutableArray.Create(new RuleFinding(path, "semantic declaration identities and types are frozen"));
    }

    private static ImmutableArray<RuleFinding> Generality(RuleEvaluationContext context)
    {
        var headers = FormalFiles(context.Current)
            .Select(item => (item.Path, Header: TryHeader(item.File.Text, out var header) ? header : null))
            .Where(static item => item.Header is not null)
            .ToDictionary(static item => item.Path.Value, static item => item.Header, StringComparer.Ordinal);
        var imports = context.Lean.Report.Files.ToDictionary(
            static item => item.Key.Value,
            static item => item.Value.Imports
                .Where(static module => module.StartsWith("D5.", StringComparison.Ordinal))
                .Select(static module => module.Replace('.', '/') + ".lean")
                .ToImmutableArray(),
            StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (source, header) in headers)
        {
            if (header?.Generality != "G")
            {
                continue;
            }

            foreach (var target in ImportClosure(source, imports))
            {
                if (headers.TryGetValue(target, out var imported)
                    && imported?.Generality is "I" or "E")
                {
                    findings.Add(new RuleFinding(
                        source,
                        $"G artifact imports {imported.Generality} fact {target}"));
                }
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Domains(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var path in context.Current.Files.Keys)
        {
            var parts = path.Value.Split('/');
            int stratumIndex;
            string label;
            if (parts.Length >= 4 && parts[0] == "D5")
            {
                stratumIndex = 1;
                label = "domain";
            }
            else if (parts.Length >= 5
                && (parts[0] is "Blueprint" or "Evidence")
                && parts[1] == "D5")
            {
                stratumIndex = 2;
                label = parts[0] == "Blueprint" ? "mirror domain" : "domain";
            }
            else
            {
                continue;
            }

            if (!IsStratum(parts[stratumIndex]))
            {
                continue;
            }

            var stratum = parts[stratumIndex];
            var domain = parts[stratumIndex + 1];
            var policyDomain = context.Policy.Domains.FirstOrDefault(
                item => string.Equals(item.Key.Value, domain, StringComparison.Ordinal));
            if (policyDomain.Key is null)
            {
                findings.Add(new RuleFinding(path.Value, $"{label} '{domain}' is not controlled"));
            }
            else if (!string.Equals(policyDomain.Value.ToString(), stratum, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"domain {domain} belongs to {policyDomain.Value}, not {stratum}"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Headers(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var headers = new List<(RepoPath Path, HeaderData Header)>();
        var counts = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var (path, file) in FormalFiles(context.Current))
        {
            if (!TryHeader(file.Text, out var header))
            {
                findings.Add(new RuleFinding(path.Value, "expected the exact six-line header at byte zero"));
                continue;
            }

            headers.Add((path, header));
            counts[header.Gid] = counts.GetValueOrDefault(header.Gid) + 1;
        }

        foreach (var (path, header) in headers)
        {
            var expected = path.Value[..^5];
            if (counts[header.Gid] == 1
                && Gid.TryParse(header.Gid, out _)
                && !string.Equals(header.Gid, expected, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(path.Value, $"GID '{header.Gid}' does not match '{expected}'"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Tasks(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var current = CollectTasks(context.Current, findings);
        var baseline = CollectTasks(context.Baseline, null);
        foreach (var duplicate in current.Where(static item => item.Value.Count > 1))
        {
            findings.Add(new RuleFinding(duplicate.Value[0].Path, $"task code {duplicate.Key} is duplicated"));
        }

        foreach (var (code, entries) in baseline)
        {
            if (!current.TryGetValue(code, out var currentEntries))
            {
                findings.Add(new RuleFinding(entries[0].Path, $"permanent task code {code} was removed"));
            }
            else if (entries[0].Autopsy != "none"
                && !currentEntries[0].Autopsy.Contains(entries[0].Autopsy, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(currentEntries[0].Path, $"autopsy for {code} was shortened"));
            }
        }

        return findings.ToImmutable();
    }

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
                    if (!SafeFieldPattern.IsMatch(anchor))
                    {
                        findings.Add(new RuleFinding(path.Value, $"anchor '{anchor}' is not machine-safe"));
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

        var tasks = CollectTasks(context.Current, null).Keys.ToHashSet(StringComparer.Ordinal);
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
            if (target is null || !Gid.TryParse(target, out _))
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

            var hasIdentifier = query.TryGetValue("doi", out var rawDoi)
                    && rawDoi is string doi
                    && DoiPattern.IsMatch(doi)
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
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        const string legacy = "Evidence/D5/values.legacy.json";
        foreach (var path in context.Current.Files.Keys
            .Where(static path => path.Value.StartsWith("Evidence/D5/values.", StringComparison.Ordinal)
                && path.Value != legacy))
        {
            findings.Add(new RuleFinding(path.Value, "values producer attestation is delayed under D5-T0003"));
        }

        if (!context.Current.TryGetFile(legacy, out var file))
        {
            return findings.ToImmutable();
        }

        try
        {
            using var document = JsonDocument.Parse(file.Text);
            if (document.RootElement.ValueKind != JsonValueKind.Object
                || document.RootElement.EnumerateObject().Any(static property =>
                    property.Value.ValueKind != JsonValueKind.Object
                    || !property.Value.TryGetProperty("status", out var status)
                    || status.GetString() != "legacy-import-unverified"))
            {
                findings.Add(new RuleFinding(legacy, "legacy values must remain explicitly unverified"));
            }
        }
        catch (JsonException)
        {
            findings.Add(new RuleFinding(legacy, "legacy values JSON is malformed"));
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Ledger(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var tasks = CollectTasks(context.Current, null).Keys.ToHashSet(StringComparer.Ordinal);
        foreach (var (path, file) in context.Current.Files)
        {
            var governed = IsGovernedStructured(path, context.Policy);
            if (governed)
            {
                if (file.HasBom)
                {
                    findings.Add(new RuleFinding(path.Value, "structured artifact must not start with a BOM"));
                    continue;
                }

                if (file.HasTrailingWhitespace || file.HasCarriageReturn)
                {
                    var lines = file.Text.Split('\n');
                    var lineNumber = Array.FindIndex(
                        lines,
                        static line => line.EndsWith(' ') || line.EndsWith('\t') || line.EndsWith('\r')) + 1;
                    findings.Add(new RuleFinding(
                        path.Value,
                        $"structured artifact has trailing whitespace on line {lineNumber}"));
                    continue;
                }

                if (!file.Text.EndsWith('\n') || file.Text.EndsWith("\n\n", StringComparison.Ordinal))
                {
                    findings.Add(new RuleFinding(path.Value, "structured artifact must end with exactly one LF"));
                    continue;
                }
            }

            if (path.Value.EndsWith(".json", StringComparison.Ordinal))
            {
                try
                {
                    using var document = JsonDocument.Parse(file.Text.TrimStart('\uFEFF'));
                    ScanJson(
                        path.Value,
                        document.RootElement,
                        "$",
                        tasks,
                        findings,
                        scanStrings: governed,
                        enforceKeyOrder: governed);
                }
                catch (JsonException)
                {
                    if (governed)
                    {
                        findings.Add(new RuleFinding(path.Value, "structured anomaly scan cannot parse JSON"));
                    }
                }
            }
            else if (path.Value.EndsWith((".yaml"), StringComparison.Ordinal)
                || path.Value.EndsWith((".yml"), StringComparison.Ordinal))
            {
                ScanYaml(path.Value, file.Text, tasks, findings, governed);
            }
            else if (path.Value.StartsWith("Chronicle/", StringComparison.Ordinal))
            {
                ScanLedgerBlocks(path.Value, file.Text, tasks, findings);
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Axioms(RuleEvaluationContext context)
    {
        const string debtPath = "D5/X_Assumptions/AxiomDebt.lean";
        var registered = ImmutableHashSet<string>.Empty;
        if (RepoPath.TryCreate(debtPath, out var debtRepoPath)
            && context.Lean.Report.Files.TryGetValue(debtRepoPath, out var debt))
        {
            registered = debt.Declarations
                .Where(static declaration => declaration.Kind == "axiom")
                .Select(static declaration => declaration.Name)
                .ToImmutableHashSet(StringComparer.Ordinal);
        }

        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, report) in context.Lean.Report.Files)
        {
            if (!string.IsNullOrEmpty(report.Error))
            {
                findings.Add(new RuleFinding(path.Value, $"Lean environment inspection failed: {report.Error}"));
                continue;
            }

            var direct = report.Declarations
                .Where(static declaration => declaration.Kind == "axiom")
                .Select(static declaration => declaration.Name)
                .ToImmutableHashSet(StringComparer.Ordinal);
            if (path.Value != debtPath && direct.Count > 0)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "axiom declarations are confined to AxiomDebt.lean: "
                    + string.Join(", ", direct.Order(StringComparer.Ordinal))));
            }

            var extra = report.Declarations
                .SelectMany(static declaration => declaration.Axioms)
                .Where(axiom => axiom != "sorryAx"
                    && !direct.Contains(axiom)
                    && !registered.Contains(axiom)
                    && !LeanAxiomFacts.IsStandard(axiom))
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (extra.Length > 0)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "unregistered transitive axiom closure: " + string.Join(", ", extra)));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Instantiation(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var path in context.Current.Files.Keys)
        {
            var parts = path.Value.Split('/');
            var theory = parts.Length > 1 && (parts[0] is "Blueprint" or "Evidence")
                ? parts[1]
                : parts[0];
            if (theory is "Metallic" or "Moduli"
                || theory.Length > 1 && theory[0] == 'D' && theory != "D5" && theory[1..].All(char.IsDigit))
            {
                findings.Add(new RuleFinding(path.Value, $"{theory} 未实例化(压力未至,D5-T0009)"));
            }
            else if (path.Value is "Meta/split.py" or "Meta/papergen")
            {
                var caseId = path.Value.EndsWith("split.py", StringComparison.Ordinal) ? "D5-T0004" : "D5-T0005";
                findings.Add(new RuleFinding(path.Value, $"{path.Value} 未实例化(案号 {caseId})"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Bootstrap(RuleEvaluationContext context) =>
        context.Changes.Paths
            .Where(BootstrapGate.IsProtected)
            .Select(static path => new RuleFinding(path.Value, "meta change requires external human review"))
            .ToImmutableArray();

    private static bool ImportAllowed(string source, string target)
    {
        if (source == "Trureturing.lean")
        {
            return target.StartsWith("D5/", StringComparison.Ordinal)
                && !target.Contains("/X_Frontier/", StringComparison.Ordinal);
        }

        var sourceParts = source.Split('/');
        var targetParts = target.Split('/');
        if (sourceParts.Length < 3 || targetParts.Length < 3)
        {
            return false;
        }

        var sourceZone = sourceParts[1];
        var targetZone = targetParts[1];
        if (sourceZone == "X_Frontier") return true;
        if (targetZone == "X_Frontier") return false;
        if (IsStratum(sourceZone))
        {
            return IsStratum(targetZone) && targetZone[1] <= sourceZone[1];
        }

        return sourceZone switch
        {
            "X_Assumptions" => IsStratum(targetZone),
            "X_Certificates" => IsStratum(targetZone) || targetZone == "X_Assumptions",
            _ => false,
        };
    }

    private static bool IsStratum(string value) => value is "S0" or "S1" or "S2" or "S3" or "S4";

    private static bool IsStatusScope(string path) => path.StartsWith(
        new[] { "D5/", "Blueprint/", "Evidence/", "Library/", "Papers/", "Chronicle/" },
        StringComparison.Ordinal);

    private static IEnumerable<(RepoPath Path, RepositoryFile File)> FormalFiles(RepositorySnapshot snapshot) =>
        snapshot.Files
            .Where(static item => item.Key.Value.StartsWith("D5/", StringComparison.Ordinal)
                && item.Key.Value.EndsWith(".lean", StringComparison.Ordinal))
            .Select(static item => (item.Key, item.Value));

    private static bool TryHeader(string text, out HeaderData header)
    {
        var match = HeaderPattern.Match(text);
        if (!match.Success || string.IsNullOrWhiteSpace(match.Groups["digest"].Value))
        {
            header = HeaderData.Empty;
            return false;
        }

        header = new HeaderData(
            match.Groups["gid"].Value.Trim(),
            match.Groups["generality"].Value,
            match.Groups["mirrorB"].Value.Trim(),
            match.Groups["mirrorE"].Value.Trim(),
            match.Groups["anchors"].Value.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries));
        return true;
    }

    private static void ValidateMirror(
        string source,
        string label,
        string value,
        string prefix,
        RepositorySnapshot snapshot,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (value.StartsWith("none(waiver:", StringComparison.Ordinal) && value.EndsWith(')'))
        {
            if (string.IsNullOrWhiteSpace(value["none(waiver:".Length..^1]))
            {
                findings.Add(new RuleFinding(source, $"{label} waiver has no reason"));
            }

            return;
        }

        if (!value.StartsWith(prefix, StringComparison.Ordinal) || !Gid.TryParse(value, out var gid))
        {
            findings.Add(new RuleFinding(source, $"{label} must be a full GID or explicit waiver"));
            return;
        }

        if (!snapshot.TryGetFile(gid.Path.Value, out _))
        {
            var kind = label == "mirror-E" ? "evidence mirror" : "mirror";
            findings.Add(new RuleFinding(source, $"missing {kind} {gid.Path.Value}"));
        }
    }

    private static HashSet<string> ImportClosure(
        string source,
        IReadOnlyDictionary<string, ImmutableArray<string>> imports)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var stack = new Stack<string>(imports.GetValueOrDefault(source, ImmutableArray<string>.Empty));
        while (stack.TryPop(out var target))
        {
            if (!seen.Add(target)) continue;
            foreach (var nested in imports.GetValueOrDefault(target, ImmutableArray<string>.Empty))
            {
                stack.Push(nested);
            }
        }

        return seen;
    }

    private static Dictionary<string, List<TaskEntry>> CollectTasks(
        RepositorySnapshot snapshot,
        ImmutableArray<RuleFinding>.Builder? findings)
    {
        var result = new Dictionary<string, List<TaskEntry>>(StringComparer.Ordinal);
        foreach (var (path, file) in FormalFiles(snapshot)
            .OrderBy(static item => item.Path.Value, StringComparer.Ordinal))
        {
            var tokens = TaskTokenPattern.Matches(file.Text);
            var matches = TaskPattern.Matches(file.Text);
            if (findings is not null && tokens.Count != matches.Count)
            {
                findings.Add(new RuleFinding(path.Value, "task block does not match the A7 grammar"));
            }

            foreach (Match match in matches)
            {
                var code = match.Groups["code"].Value;
                if (!result.TryGetValue(code, out var entries))
                {
                    entries = new List<TaskEntry>();
                    result.Add(code, entries);
                }

                entries.Add(new TaskEntry(path.Value, match.Groups["autopsy"].Value.Trim()));
            }
        }

        return result;
    }

    private static void ValidateFormulas(
        string path,
        string text,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        try
        {
            using var document = JsonDocument.Parse(text.TrimStart('\uFEFF'));
            WalkFormula(document.RootElement, path, findings);
        }
        catch (JsonException exception)
        {
            findings.Add(new RuleFinding(path, $"invalid JSON: {exception.Message}"));
        }
    }

    private static void WalkFormula(
        JsonElement element,
        string path,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (element.ValueKind == JsonValueKind.Object)
        {
            if (element.TryGetProperty("formula", out var formula))
            {
                if (formula.ValueKind != JsonValueKind.String
                    || !element.TryGetProperty("refs", out var refs)
                    || refs.ValueKind != JsonValueKind.Object)
                {
                    findings.Add(new RuleFinding(path, "formula and refs must be string/object"));
                }
                else
                {
                    try
                    {
                        FormulaValidator.Validate(
                            formula.GetString() ?? string.Empty,
                            refs.EnumerateObject().Select(static item => item.Name).ToHashSet(StringComparer.Ordinal));
                    }
                    catch (FormatException exception)
                    {
                        findings.Add(new RuleFinding(path, exception.Message));
                    }
                }
            }

            foreach (var property in element.EnumerateObject()) WalkFormula(property.Value, path, findings);
        }
        else if (element.ValueKind == JsonValueKind.Array)
        {
            foreach (var child in element.EnumerateArray()) WalkFormula(child, path, findings);
        }
    }

    private static IEnumerable<string> SplitYamlListBlocks(string text)
    {
        var matches = Regex.Matches(text, "(?ms)^  - (?<body>.*?)(?=^  - |\\z)");
        return matches.Select(static match => match.Groups["body"].Value);
    }

    private static Dictionary<string, string> SimpleYamlFields(string block)
    {
        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var line in block.Split('\n'))
        {
            var match = Regex.Match(line.Trim(), "^(?:- )?(?<key>[A-Za-z_][A-Za-z0-9_.-]*):\\s*(?<value>.*)$");
            if (match.Success)
            {
                result[match.Groups["key"].Value] = match.Groups["value"].Value.Trim().Trim('"', '\'');
            }
        }

        return result;
    }

    private static bool IsGovernedStructured(RepoPath path, ValidatedPolicy policy) =>
        RepositoryPathPolicy.TryResolve(path, policy, out _)
        && (path.Value.EndsWith(".json", StringComparison.Ordinal)
            || path.Value.EndsWith(".yaml", StringComparison.Ordinal)
            || path.Value.EndsWith(".yml", StringComparison.Ordinal));

    private static void ScanJson(
        string path,
        JsonElement element,
        string location,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings,
        bool scanStrings,
        bool enforceKeyOrder)
    {
        if (element.ValueKind == JsonValueKind.Object)
        {
            var properties = element.EnumerateObject().ToArray();
            if (enforceKeyOrder && !properties.Select(static item => item.Name)
                .SequenceEqual(properties.Select(static item => item.Name).Order(StringComparer.Ordinal)))
            {
                findings.Add(new RuleFinding(path, $"object keys are not sorted at {location}"));
                return;
            }

            var classification = ClassifyAnomaly(element);
            if (classification is "unknown")
            {
                findings.Add(new RuleFinding(path, $"unknown anomaly-bearing schema at {location}"));
                return;
            }

            if (classification is "open")
            {
                var caseId = element.TryGetProperty("case_id", out var caseValue)
                    ? caseValue.GetString()
                    : element.TryGetProperty("case", out caseValue) ? caseValue.GetString() : null;
                if (caseId is null || !CasePattern.IsMatch(caseId) || !tasks.Contains(caseId))
                {
                    findings.Add(new RuleFinding(path, $"unledgered anomaly at {location}"));
                }
            }

            foreach (var property in properties)
            {
                if (classification is not null && AnomalySchemaKeys.Contains(property.Name))
                {
                    continue;
                }

                ScanJson(
                    path,
                    property.Value,
                    $"{location}.{property.Name}",
                    tasks,
                    findings,
                    scanStrings,
                    enforceKeyOrder);
            }
        }
        else if (element.ValueKind == JsonValueKind.Array)
        {
            var index = 0;
            foreach (var child in element.EnumerateArray())
            {
                ScanJson(
                    path,
                    child,
                    $"{location}[{index++}]",
                    tasks,
                    findings,
                    scanStrings,
                    enforceKeyOrder);
            }
        }
        else if (scanStrings && element.ValueKind == JsonValueKind.String)
        {
            ScanSerializedString(path, element.GetString() ?? string.Empty, location, tasks, findings);
        }
    }

    private static string? ClassifyAnomaly(JsonElement record)
    {
        if (record.TryGetProperty("kind", out var kindElement) && kindElement.ValueKind == JsonValueKind.String)
        {
            var kind = kindElement.GetString() ?? string.Empty;
            if (AnomalyKindPattern.IsMatch(kind))
            {
                var state = record.TryGetProperty("state", out var stateElement) ? stateElement.GetString() : null;
                return state switch { "resolved" => "closed", "unresolved" => "open", _ => "unknown" };
            }

            if (AnomalyBearingPattern.IsMatch(kind)) return "unknown";
        }

        foreach (var key in new[] { "type", "category", "record_type" })
        {
            if (record.TryGetProperty(key, out var value)
                && value.ValueKind == JsonValueKind.String
                && AnomalyBearingPattern.IsMatch(value.GetString() ?? string.Empty))
            {
                return "unknown";
            }
        }

        if (new[] { "anomalies", "exceptions", "failures", "tensions" }
            .Any(key => record.TryGetProperty(key, out _))) return "unknown";
        if (new[] { "anomaly", "exception", "failure", "tension", "unresolved" }
            .Any(key => record.TryGetProperty(key, out var value) && IsOpen(value))) return "open";
        return null;
    }

    private static bool IsOpen(JsonElement value) => value.ValueKind switch
    {
        JsonValueKind.Null or JsonValueKind.False => false,
        JsonValueKind.String => value.GetString() is not ("" or "none" or "resolved"),
        JsonValueKind.Array => value.GetArrayLength() > 0,
        JsonValueKind.Object => value.EnumerateObject().Any(),
        _ => true,
    };

    private static void ScanSerializedString(
        string path,
        string value,
        string location,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        var normalized = value.Replace("\uFEFF", string.Empty, StringComparison.Ordinal).Trim();
        var opaque = new List<string>();
        var cursor = 0;
        var index = 0;
        while (index < normalized.Length)
        {
            if (normalized[index] is not ('{' or '['))
            {
                index++;
                continue;
            }

            if (!TryParseEmbeddedJson(normalized, index, out var document, out var consumed)
                || document is null)
            {
                index++;
                continue;
            }

            using (document)
            {
                opaque.Add(normalized[cursor..index]);
                ScanJson(
                    path,
                    document.RootElement,
                    location,
                    tasks,
                    findings,
                    scanStrings: true,
                    enforceKeyOrder: false);
            }

            cursor = index + consumed;
            index = cursor;
        }

        opaque.Add(normalized[cursor..]);

        var unescaped = Regex.Replace(
            string.Join('\n', opaque),
            "\\\\u([0-9a-fA-F]{4})",
            static match => ((char)Convert.ToInt32(match.Groups[1].Value, 16)).ToString());
        if (AnomalyBearingPattern.IsMatch(unescaped)
            || Regex.IsMatch(unescaped, "\\\"(?:kind|type|category|record_type)\\\"\\s*:"))
        {
            findings.Add(new RuleFinding(path, $"unknown anomaly-bearing schema at {location}"));
        }
    }

    private static bool TryParseEmbeddedJson(
        string value,
        int start,
        out JsonDocument? document,
        out int consumedCharacters)
    {
        var bytes = Encoding.UTF8.GetBytes(value[start..]);
        var reader = new Utf8JsonReader(bytes, isFinalBlock: true, state: default);
        try
        {
            document = JsonDocument.ParseValue(ref reader);
            if (document.RootElement.ValueKind is not (JsonValueKind.Object or JsonValueKind.Array))
            {
                document.Dispose();
                document = null;
                consumedCharacters = 0;
                return false;
            }

            consumedCharacters = Encoding.UTF8.GetCharCount(bytes.AsSpan(0, checked((int)reader.BytesConsumed)));
            return true;
        }
        catch (JsonException)
        {
            document = null;
            consumedCharacters = 0;
            return false;
        }
    }

    private static void ScanYaml(
        string path,
        string text,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings,
        bool enforceKeyOrder)
    {
        try
        {
            var value = YamlSubsetParser.Parse(text);
            var element = JsonSerializer.SerializeToElement(value);
            ScanJson(
                path,
                element,
                "$",
                tasks,
                findings,
                scanStrings: true,
                enforceKeyOrder: enforceKeyOrder);
        }
        catch (FormatException exception)
        {
            findings.Add(new RuleFinding(path, $"structured anomaly scan cannot parse YAML: {exception.Message}"));
        }
    }

    private static void ScanLedgerBlocks(
        string path,
        string text,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        var matches = Regex.Matches(text, "(?s)<!-- STRATALINT-LEDGER\\n(?<body>.*?)\\n-->");
        var index = 0;
        foreach (Match match in matches)
        {
            index++;
            try
            {
                using var document = JsonDocument.Parse(match.Groups["body"].Value);
                ScanJson(
                    path,
                    document.RootElement,
                    $"ledger block {index}:$",
                    tasks,
                    findings,
                    scanStrings: true,
                    enforceKeyOrder: false);
            }
            catch (JsonException)
            {
                findings.Add(new RuleFinding(path, $"invalid structured ledger block {index}"));
            }
        }
    }

    private sealed record HeaderData(
        string Gid,
        string Generality,
        string MirrorB,
        string MirrorE,
        string[] Anchors)
    {
        internal static HeaderData Empty { get; } = new(string.Empty, string.Empty, string.Empty, string.Empty, Array.Empty<string>());
    }

    private sealed record TaskEntry(string Path, string Autopsy);

    private sealed class FormulaValidator
    {
        private static readonly Regex TokenPattern = new(
            "\\G\\s*(?:(?<number>[0-9]+(?:\\.[0-9]+)?)|(?<name>[A-Za-z][A-Za-z0-9_.]*)|(?<symbol>.))",
            RegexOptions.CultureInvariant);

        private readonly List<(string Kind, string Value)> tokens;
        private readonly IReadOnlySet<string> references;
        private int index;

        private FormulaValidator(string source, IReadOnlySet<string> references)
        {
            if (!source.All(static character => character <= 0x7f))
            {
                throw new FormatException("formula must be ASCII");
            }

            this.references = references;
            tokens = new List<(string Kind, string Value)>();
            var position = 0;
            while (position < source.Length)
            {
                var match = TokenPattern.Match(source, position);
                if (!match.Success || match.Index != position)
                {
                    throw new FormatException("formula tokenization failed");
                }

                position += match.Length;
                if (match.Groups["number"].Success) tokens.Add(("number", match.Groups["number"].Value));
                else if (match.Groups["name"].Success) tokens.Add(("name", match.Groups["name"].Value));
                else
                {
                    var symbol = match.Groups["symbol"].Value;
                    if (symbol is not ("+" or "-" or "*" or "/" or "(" or ")"))
                    {
                        throw new FormatException($"illegal formula character '{symbol}'");
                    }

                    tokens.Add((symbol, symbol));
                }
            }
        }

        internal static void Validate(string source, IReadOnlySet<string> references)
        {
            var parser = new FormulaValidator(source.Trim(), references);
            parser.Expression();
            if (parser.index != parser.tokens.Count) throw new FormatException("trailing formula tokens");
        }

        private void Expression()
        {
            Term();
            while (Take("+") || Take("-")) Term();
        }

        private void Term()
        {
            Factor();
            while (Take("*") || Take("/")) Factor();
        }

        private void Factor()
        {
            if (Take("+") || Take("-")) { Factor(); return; }
            if (Take("number")) return;
            if (index < tokens.Count && tokens[index].Kind == "name")
            {
                var name = tokens[index++].Value;
                if (name == "sqrt")
                {
                    if (!Take("(")) throw new FormatException("sqrt requires parentheses");
                    Expression();
                    if (!Take(")")) throw new FormatException("sqrt is missing a closing parenthesis");
                }
                else if (!references.Contains(name))
                {
                    throw new FormatException($"unbound formula ref {name}");
                }

                return;
            }

            if (Take("("))
            {
                Expression();
                if (!Take(")")) throw new FormatException("missing closing parenthesis");
                return;
            }

            throw new FormatException("expected formula factor");
        }

        private bool Take(string kind)
        {
            if (index >= tokens.Count || tokens[index].Kind != kind) return false;
            index++;
            return true;
        }
    }
}

internal static class StringExtensions
{
    internal static bool StartsWith(
        this string value,
        IEnumerable<string> prefixes,
        StringComparison comparison) =>
        prefixes.Any(prefix => value.StartsWith(prefix, comparison));
}

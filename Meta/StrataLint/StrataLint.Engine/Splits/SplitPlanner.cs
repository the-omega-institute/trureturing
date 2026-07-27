using System.Collections.Immutable;
using System.Globalization;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal enum SplitPlanStatus
{
    Pending,
    Applied,
    AlreadyApplied,
}

internal sealed record SplitRequest(
    string SourceDirectory,
    string DestinationDomain,
    string Date,
    string BaseRevision);

internal sealed record SplitMove(string Source, string Target);

internal sealed record SplitWrite(string Path, string Text);

internal sealed record SplitPlan(
    SplitPlanStatus Status,
    string ReceiptSha256,
    string BaseRevision,
    string Date,
    string SourceDirectory,
    string DestinationDirectory,
    ImmutableArray<SplitMove> Moves,
    ImmutableArray<SplitWrite> Writes,
    ImmutableArray<string> PreservedBaseMappings,
    ImmutableArray<string> Derivations);

internal sealed class SplitPlanException(string message) : Exception(message);

internal static class SplitPlanner
{
    private const int MaximumFiles = 12;
    private static readonly Regex StratumPattern = new("^S[0-4]$", RegexOptions.CultureInvariant);
    private static readonly Regex ReceiptPattern = new(
        "<!-- stratalint-split receipt=(?<receipt>sha256:[0-9a-f]{64}) base=(?<base>[0-9a-f]{40}|[0-9a-f]{64}) date=(?<date>[0-9]{4}-[0-9]{2}-[0-9]{2}) source=(?<source>[A-Za-z0-9_./-]+) destination=(?<destination>[A-Za-z0-9_./-]+) additions=(?<additions>[A-Za-z0-9_.-]+(?:,[A-Za-z0-9_.-]+)*) -->",
        RegexOptions.CultureInvariant);

    internal static SplitPlan Plan(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        SplitRequest request)
    {
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(policy);
        ArgumentNullException.ThrowIfNull(request);
        ValidateRequest(request);

        var shape = SplitShape.Parse(policy, request.SourceDirectory, request.DestinationDomain);
        var currentSource = DirectFiles(current, shape.SourceDirectory);
        var baselineSource = DirectFiles(baseline, shape.SourceDirectory);
        var preserved = baselineSource.Order(StringComparer.Ordinal).ToImmutableArray();
        var existingMap = current.TryGetFile(shape.MapPath, out var map) ? map.Text : string.Empty;
        var previous = FindReceipt(existingMap, request, shape);
        if (previous is not null)
        {
            return AlreadyApplied(current, baseline, policy, request, shape, preserved, previous);
        }

        if (currentSource.Length <= MaximumFiles)
        {
            throw new SplitPlanException(
                $"source directory {shape.SourceDirectory} contains {currentSource.Length} files; split requires more than {MaximumFiles}");
        }

        if (baselineSource.Length > MaximumFiles)
        {
            throw new SplitPlanException(
                $"source directory already contained {baselineSource.Length} base files; moving them requires explicit migration with attestation re-emission");
        }

        var pressure = currentSource.Except(baselineSource, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        if (pressure.Length == 0 || currentSource.Length - pressure.Length > MaximumFiles)
        {
            throw new SplitPlanException(
                "the overflow cannot be resolved from pressure-causing additions alone; explicit migration is required");
        }

        var primaryMoves = pressure.Select(path => PrimaryMove(policy, shape, path)).ToImmutableArray();
        return BuildPlan(
            current,
            baseline,
            request,
            shape,
            preserved,
            primaryMoves,
            SplitPlanStatus.Pending);
    }

    private static SplitPlan AlreadyApplied(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        SplitRequest request,
        SplitShape shape,
        ImmutableArray<string> preserved,
        ReceiptData receipt)
    {
        var primaryMoves = receipt.Additions
            .Select(fileName => PrimaryMove(
                policy,
                shape,
                shape.SourceDirectory + "/" + fileName))
            .ToImmutableArray();
        foreach (var move in primaryMoves)
        {
            if (current.TryGetFile(move.Source, out _)
                || !current.TryGetFile(move.Target, out _)
                || baseline.TryGetFile(move.Target, out _))
            {
                throw new SplitPlanException(
                    $"split receipt {receipt.ReceiptSha256} does not match the current source/destination state");
            }
        }

        foreach (var path in preserved)
        {
            if (!current.TryGetFile(path, out _))
            {
                throw new SplitPlanException(
                    $"pre-existing path {path} moved after split; explicit migration is required");
            }
        }

        var plan = BuildPlan(
            current,
            baseline,
            request,
            shape,
            preserved,
            primaryMoves,
            SplitPlanStatus.AlreadyApplied,
            includeWrites: false);
        if (!string.Equals(plan.ReceiptSha256, receipt.ReceiptSha256, StringComparison.Ordinal))
        {
            throw new SplitPlanException("split receipt fingerprint does not match the deterministic plan");
        }

        return plan;
    }

    private static SplitPlan BuildPlan(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        SplitRequest request,
        SplitShape shape,
        ImmutableArray<string> preserved,
        ImmutableArray<SplitMove> primaryMoves,
        SplitPlanStatus status,
        bool includeWrites = true)
    {
        var moves = ExpandMoves(current, baseline, shape, primaryMoves);
        if (status is not SplitPlanStatus.AlreadyApplied)
        {
            ValidateTargets(current, moves);
        }
        var receipt = Fingerprint(request, shape, primaryMoves);
        if (!includeWrites)
        {
            return new SplitPlan(
                status,
                receipt,
                request.BaseRevision,
                request.Date,
                shape.SourceDirectory,
                shape.DestinationDirectory,
                moves,
                ImmutableArray<SplitWrite>.Empty,
                preserved,
                DerivationCommands(request.BaseRevision));
        }

        var replacements = Replacements(shape, primaryMoves);
        var moveBySource = moves.ToDictionary(static move => move.Source, StringComparer.Ordinal);
        var writes = ImmutableArray.CreateBuilder<SplitWrite>();
        foreach (var (path, file) in current.Files.OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
        {
            if (file.IsOpaque)
            {
                if (moveBySource.ContainsKey(path.Value))
                {
                    throw new SplitPlanException($"split cannot rewrite opaque file {path.Value}");
                }

                continue;
            }

            var target = moveBySource.TryGetValue(path.Value, out var move) ? move.Target : path.Value;
            var rewritten = ApplyReplacements(file.Text, replacements);
            if (move is not null && move.Source.EndsWith(".scribe.cs", StringComparison.Ordinal))
            {
                rewritten = rewritten.Replace(
                    shape.SourceScribeNamespace,
                    shape.DestinationScribeNamespace,
                    StringComparison.Ordinal);
            }

            if (target != path.Value || rewritten != file.Text)
            {
                writes.Add(new SplitWrite(target, rewritten));
            }
        }

        var mapText = AppendMap(
            current.TryGetFile(shape.MapPath, out var map) ? map.Text : string.Empty,
            request,
            shape,
            primaryMoves,
            preserved.Length,
            receipt);
        for (var index = 0; index < writes.Count; index++)
        {
            if (writes[index].Path == shape.MapPath)
            {
                writes.RemoveAt(index);
                break;
            }
        }

        writes.Add(new SplitWrite(shape.MapPath, mapText));
        return new SplitPlan(
            status,
            receipt,
            request.BaseRevision,
            request.Date,
            shape.SourceDirectory,
            shape.DestinationDirectory,
            moves,
            writes.OrderBy(static write => write.Path, StringComparer.Ordinal).ToImmutableArray(),
            preserved,
            DerivationCommands(request.BaseRevision));
    }

    private static ImmutableArray<SplitMove> ExpandMoves(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        SplitShape shape,
        ImmutableArray<SplitMove> primaryMoves)
    {
        var moves = ImmutableArray.CreateBuilder<SplitMove>();
        foreach (var primary in primaryMoves)
        {
            moves.Add(primary);
            if (shape.Kind is not SplitKind.Formal)
            {
                continue;
            }

            var oldCoordinates = primary.Source[3..^5];
            var newCoordinates = primary.Target[3..^5];
            foreach (var path in current.Files.Keys.Select(static item => item.Value).Order(StringComparer.Ordinal))
            {
                var blueprintBase = $"Blueprint/D5/{oldCoordinates}";
                var isBlueprint = path == blueprintBase + ".md"
                    || path == blueprintBase + ".scribe.cs";
                var isEvidence = path.StartsWith($"Evidence/D5/{oldCoordinates}.", StringComparison.Ordinal);
                if (!isBlueprint && !isEvidence)
                {
                    continue;
                }

                if (baseline.TryGetFile(path, out _))
                {
                    throw new SplitPlanException(
                        $"companion {path} existed in the base; moving it requires explicit migration with GID attestation re-emission");
                }

                var target = isBlueprint
                    ? path.Replace(
                        $"Blueprint/D5/{oldCoordinates}",
                        $"Blueprint/D5/{newCoordinates}",
                        StringComparison.Ordinal)
                    : path.Replace(
                        $"Evidence/D5/{oldCoordinates}",
                        $"Evidence/D5/{newCoordinates}",
                        StringComparison.Ordinal);
                moves.Add(new SplitMove(path, target));
            }
        }

        return moves.Distinct().OrderBy(static move => move.Source, StringComparer.Ordinal).ToImmutableArray();
    }

    private static ImmutableArray<(string Old, string New)> Replacements(
        SplitShape shape,
        ImmutableArray<SplitMove> primaryMoves)
    {
        var replacements = ImmutableArray.CreateBuilder<(string Old, string New)>();
        foreach (var move in primaryMoves)
        {
            if (shape.Kind is SplitKind.Library)
            {
                var module = Path.GetFileNameWithoutExtension(move.Source);
                replacements.Add(($"D5/L/{module}", $"D5/L/{shape.DestinationDomain}/{module}"));
                continue;
            }

            var oldGid = move.Source[3..^5];
            var newGid = move.Target[3..^5];
            replacements.Add(($"D5/B/{oldGid}", $"D5/B/{newGid}"));
            replacements.Add(($"D5/E/{oldGid}", $"D5/E/{newGid}"));
            replacements.Add(($"D5/{oldGid}", $"D5/{newGid}"));
            replacements.Add(($"D5.{oldGid.Replace('/', '.')}", $"D5.{newGid.Replace('/', '.')}"));
        }

        return replacements
            .Distinct()
            .OrderByDescending(static pair => pair.Old.Length)
            .ThenBy(static pair => pair.Old, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static string ApplyReplacements(
        string text,
        ImmutableArray<(string Old, string New)> replacements)
    {
        foreach (var (oldValue, newValue) in replacements)
        {
            var suffix = oldValue.StartsWith("D5/L/", StringComparison.Ordinal)
                ? "(?![A-Za-z0-9_.-])"
                : "(?![A-Za-z0-9_-])";
            text = Regex.Replace(
                text,
                Regex.Escape(oldValue) + suffix,
                _ => newValue,
                RegexOptions.CultureInvariant);
        }

        return text;
    }

    private static SplitMove PrimaryMove(ValidatedPolicy policy, SplitShape shape, string source)
    {
        if (DirectoryName(source) != shape.SourceDirectory)
        {
            throw new SplitPlanException($"pressure path is outside source directory: {source}");
        }

        if (shape.Kind is SplitKind.Formal && !source.EndsWith(".lean", StringComparison.Ordinal))
        {
            throw new SplitPlanException(
                $"formal split pressure path {source} is not a Lean module; explicit migration is required");
        }

        if (shape.Kind is SplitKind.Library && !source.EndsWith(".md", StringComparison.Ordinal))
        {
            throw new SplitPlanException(
                $"library split pressure path {source} is not a literature note; explicit migration is required");
        }

        var module = Path.GetFileNameWithoutExtension(source);
        var manifest = shape.Kind is SplitKind.Formal
            ? new ManifestSyntax("D5", "F", shape.DestinationDomain, module, "G", string.Empty, "lean", string.Empty)
            : new ManifestSyntax("D5", "L", shape.DestinationDomain, module, "G", string.Empty, "markdown", string.Empty);
        var outcome = RouteEngine.Route(policy, manifest);
        if (outcome is not RouteOutcome.Routed routed)
        {
            var rejected = (RouteOutcome.Rejected)outcome;
            throw new SplitPlanException(
                $"{rejected.RuleId.Value} split destination rejected by route: {rejected.Message}");
        }

        return new SplitMove(source, routed.Result.Path.Value);
    }

    private static void ValidateTargets(RepositorySnapshot current, ImmutableArray<SplitMove> moves)
    {
        var targets = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var move in moves)
        {
            if (!targets.Add(move.Target))
            {
                throw new SplitPlanException($"split target is duplicated or case-colliding: {move.Target}");
            }

            if (current.TryGetFile(move.Target, out _) && move.Source != move.Target)
            {
                throw new SplitPlanException($"split target already exists: {move.Target}");
            }
        }
    }

    private static string AppendMap(
        string existing,
        SplitRequest request,
        SplitShape shape,
        ImmutableArray<SplitMove> primaryMoves,
        int preservedCount,
        string receipt)
    {
        var sourceBucket = shape.SourceDirectory[(shape.SourceDirectory.LastIndexOf('/') + 1)..] + "/";
        var destinationBucket = shape.DestinationDomain + "/";
        var additions = string.Join(
            ", ",
            primaryMoves.Select(move => $"`{Path.GetFileName(move.Source)}`"));
        var machineAdditions = string.Join(
            ',',
            primaryMoves.Select(move => Path.GetFileName(move.Source)));
        var entry = $"- {request.Date} (SL-003): `{sourceBucket}` reached capacity; pressure-causing additions {additions} opened the registered `{destinationBucket}` bucket; all {preservedCount} base paths remain in place.\n"
            + $"  Receipt: `{receipt}`.\n"
            + $"<!-- stratalint-split receipt={receipt} base={request.BaseRevision} date={request.Date} source={shape.SourceDirectory} destination={shape.DestinationDirectory} additions={machineAdditions} -->\n";
        if (existing.Length == 0)
        {
            var title = shape.Kind is SplitKind.Library
                ? "# Library Map"
                : $"# D5 {shape.Stratum} Map";
            return title + "\n\n## Split history\n\n" + entry
                + "\n## Buckets\n\n"
                + $"- `{sourceBucket}`: original bucket; base paths remain stable.\n"
                + $"- `{destinationBucket}`: controlled domain registered in `Meta/domains.yaml`.\n";
        }

        if (existing.Contains($"receipt={receipt}", StringComparison.Ordinal))
        {
            return existing;
        }

        const string history = "## Split history\n\n";
        if (!existing.Contains(history, StringComparison.Ordinal))
        {
            throw new SplitPlanException($"existing map {shape.MapPath} has no canonical split history section");
        }

        var updated = existing.Replace(history, history + entry, StringComparison.Ordinal);
        if (!updated.Contains($"- `{destinationBucket}`:", StringComparison.Ordinal))
        {
            updated = updated.TrimEnd('\n')
                + $"\n- `{destinationBucket}`: controlled domain registered in `Meta/domains.yaml`.\n";
        }

        return updated;
    }

    private static ReceiptData? FindReceipt(string map, SplitRequest request, SplitShape shape)
    {
        foreach (Match match in ReceiptPattern.Matches(map))
        {
            if (match.Groups["base"].Value == request.BaseRevision
                && match.Groups["date"].Value == request.Date
                && match.Groups["source"].Value == shape.SourceDirectory
                && match.Groups["destination"].Value == shape.DestinationDirectory)
            {
                return new ReceiptData(
                    match.Groups["receipt"].Value,
                    match.Groups["additions"].Value.Split(',').ToImmutableArray());
            }
        }

        return null;
    }

    private static string Fingerprint(
        SplitRequest request,
        SplitShape shape,
        ImmutableArray<SplitMove> primaryMoves)
    {
        var canonical = "schema=1\n"
            + $"base={request.BaseRevision}\n"
            + $"date={request.Date}\n"
            + $"source={shape.SourceDirectory}\n"
            + $"destination={shape.DestinationDirectory}\n"
            + string.Join('\n', primaryMoves.Select(move => $"move={move.Source}->{move.Target}"))
            + "\n";
        return "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(canonical)));
    }

    private static ImmutableArray<string> DirectFiles(RepositorySnapshot snapshot, string directory) =>
        snapshot.Files.Keys
            .Select(static path => path.Value)
            .Where(path => DirectoryName(path) == directory)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();

    private static string DirectoryName(string path)
    {
        var slash = path.LastIndexOf('/');
        return slash < 0 ? "." : path[..slash];
    }

    private static ImmutableArray<string> DerivationCommands(string baseRevision) =>
        ImmutableArray.Create(
            "make lean-report",
            "make emit",
            $"make ingest BASE={baseRevision}",
            "make emit");

    private static void ValidateRequest(SplitRequest request)
    {
        if (!RepoPath.TryCreate(request.SourceDirectory, out _)
            || request.SourceDirectory.EndsWith("/", StringComparison.Ordinal))
        {
            throw new SplitPlanException("split source directory is not a canonical repository path");
        }

        if (!DomainId.TryCreate(request.DestinationDomain, out _))
        {
            throw new SplitPlanException("split destination must be a canonical registered domain");
        }

        if (!DateOnly.TryParseExact(
            request.Date,
            "yyyy-MM-dd",
            CultureInfo.InvariantCulture,
            DateTimeStyles.None,
            out _))
        {
            throw new SplitPlanException("split date must use YYYY-MM-DD");
        }

        if (request.BaseRevision.Length is not (40 or 64)
            || request.BaseRevision.Any(static character => !char.IsAsciiHexDigitLower(character)))
        {
            throw new SplitPlanException("split base revision must be an exact lowercase object ID");
        }
    }

    private sealed record ReceiptData(string ReceiptSha256, ImmutableArray<string> Additions);

    private enum SplitKind
    {
        Formal,
        Library,
    }

    private sealed record SplitShape(
        SplitKind Kind,
        string SourceDirectory,
        string DestinationDirectory,
        string DestinationDomain,
        string Stratum,
        string MapPath,
        string SourceScribeNamespace,
        string DestinationScribeNamespace)
    {
        internal static SplitShape Parse(
            ValidatedPolicy policy,
            string sourceDirectory,
            string destinationDomain)
        {
            var destination = policy.Domains.FirstOrDefault(
                item => item.Key.Value == destinationDomain);
            if (destination.Key is null)
            {
                throw new SplitPlanException(
                    $"split destination domain {destinationDomain} is not registered in Meta/domains.yaml");
            }

            var parts = sourceDirectory.Split('/');
            if (parts is ["D5", var stratum, var sourceDomain]
                && StratumPattern.IsMatch(stratum))
            {
                var source = policy.Domains.FirstOrDefault(item => item.Key.Value == sourceDomain);
                if (source.Key is null || source.Value.ToString() != stratum)
                {
                    throw new SplitPlanException(
                        $"formal split source {sourceDirectory} is not a registered domain bucket");
                }

                if (destination.Value.ToString() != stratum)
                {
                    throw new SplitPlanException(
                        $"destination domain {destinationDomain} belongs to {destination.Value}, not {stratum}");
                }

                if (sourceDomain == destinationDomain)
                {
                    throw new SplitPlanException("split destination must differ from the source domain");
                }

                return new SplitShape(
                    SplitKind.Formal,
                    sourceDirectory,
                    $"D5/{stratum}/{destinationDomain}",
                    destinationDomain,
                    stratum,
                    $"D5/{stratum}/MAP.md",
                    $"StrataLint.Scribe.Blueprint.D5.{stratum}.{sourceDomain}",
                    $"StrataLint.Scribe.Blueprint.D5.{stratum}.{destinationDomain}");
            }

            if (parts is ["Library", var librarySource])
            {
                if (librarySource != "notes"
                    && !policy.Domains.Keys.Any(item => item.Value == librarySource))
                {
                    throw new SplitPlanException(
                        $"library split source {sourceDirectory} is not notes or a registered domain bucket");
                }

                if (librarySource == destinationDomain)
                {
                    throw new SplitPlanException("split destination must differ from the source domain");
                }

                return new SplitShape(
                    SplitKind.Library,
                    sourceDirectory,
                    $"Library/{destinationDomain}",
                    destinationDomain,
                    string.Empty,
                    "Library/MAP.md",
                    string.Empty,
                    string.Empty);
            }

            throw new SplitPlanException(
                "split source must be D5/S<0-4>/<Domain> or Library/<bucket>");
        }
    }
}

internal static class SplitReceiptWriter
{
    private static readonly JsonSerializerOptions Options = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        Converters = { new JsonStringEnumConverter(JsonNamingPolicy.SnakeCaseLower) },
    };

    internal static string Write(SplitPlan plan)
    {
        var status = plan.Status switch
        {
            SplitPlanStatus.Pending => "planned",
            SplitPlanStatus.Applied => "applied",
            SplitPlanStatus.AlreadyApplied => "already_applied",
            _ => throw new InvalidOperationException("unknown split plan status"),
        };
        return JsonSerializer.Serialize(
            new
            {
                schema_version = 1,
                status,
                receipt_sha256 = plan.ReceiptSha256,
                base_revision = plan.BaseRevision,
                date = plan.Date,
                source_directory = plan.SourceDirectory,
                destination_directory = plan.DestinationDirectory,
                moves = plan.Moves.Select(static move => new { source = move.Source, target = move.Target }),
                rewritten_paths = plan.Writes.Select(static write => write.Path),
                preserved_base_paths = plan.PreservedBaseMappings,
                derivations = plan.Derivations,
            },
            Options) + "\n";
    }
}

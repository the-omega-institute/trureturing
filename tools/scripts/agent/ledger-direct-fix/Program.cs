using System.Collections.Immutable;
using System.Reflection;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

const string AcceptedRoot = "Golden/Frozen/accepted";

try
{
    var options = Options.Parse(args);
    var repositoryRoot = Path.GetFullPath(options.RepositoryRoot);
    var reportPath = Path.GetFullPath(options.CandidateLeanReport, repositoryRoot);
    var acceptedDirectory = Path.Combine(repositoryRoot, AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));

    var report = ReadReport(reportPath);
    var events = ReadEvents(acceptedDirectory);
    var eventsByPath = events.ToDictionary(static item => item.DescriptorSelector, StringComparer.Ordinal);
    var modulePaths = report.Modules.ToDictionary(static item => item.Module, static item => item.SourcePath, StringComparer.Ordinal);
    var modulesByPath = report.Modules.ToDictionary(static item => item.SourcePath, StringComparer.Ordinal);

    foreach (var descriptor in eventsByPath.Keys)
    {
        if (!modulesByPath.ContainsKey(descriptor))
        {
            throw new InvalidOperationException($"Accepted Freeze {descriptor} is absent from the candidate Lean report.");
        }
    }

    var dependencies = eventsByPath.Keys.ToDictionary(
        static path => path,
        path => ManagedDependencies(modulesByPath[path], modulePaths, eventsByPath),
        StringComparer.Ordinal);
    var canonical = ComputeCanonicalNodes(eventsByPath, dependencies);
    var stale = events
        .Select(item => StaleEvent.Create(item, canonical[item.DescriptorSelector].Prerequisites))
        .Where(static item => item.StaleEdgeCount > 0)
        .OrderBy(static item => item.Event.RepoRelativePath, StringComparer.Ordinal)
        .ToImmutableArray();
    var stalePaths = stale.Select(static item => item.Event.DescriptorSelector).ToImmutableHashSet(StringComparer.Ordinal);
    var cascadeMembers = stale
        .Where(item => dependencies[item.Event.DescriptorSelector].Any(stalePaths.Contains))
        .Select(static item => item.Event.DescriptorSelector)
        .Order(StringComparer.Ordinal)
        .ToImmutableArray();
    var staleEdges = stale.Sum(static item => item.StaleEdgeCount);

    var expectedShardPaths = options.ExpectedEnumeration is null
        ? ImmutableArray<string>.Empty
        : ReadExpectedShardPaths(options.ExpectedEnumeration);
    var actualShardPaths = stale.Select(static item => item.Event.RepoRelativePath).ToImmutableArray();
    var expectedOnly = expectedShardPaths.Except(actualShardPaths, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
    var actualOnly = actualShardPaths.Except(expectedShardPaths, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();

    if (options.ExpectClean)
    {
        if (!stale.IsEmpty || staleEdges != 0)
        {
            throw new InvalidOperationException(
                $"Expected a clean fixed point, found stale_events={stale.Length} stale_edges={staleEdges}.");
        }
    }
    else if (stale.Length != 91 || staleEdges != 131 || !expectedOnly.IsEmpty || !actualOnly.IsEmpty)
    {
        throw new InvalidOperationException(
            $"Fresh enumeration differs from the owner-approved set: stale_events={stale.Length} "
            + $"stale_edges={staleEdges} expected_only={expectedOnly.Length} actual_only={actualOnly.Length}.");
    }

    var replacements = stale.Select(item => BuildReplacement(item, canonical[item.Event.DescriptorSelector]))
        .ToImmutableArray();
    ValidateReplacementSet(events, replacements, canonical);
    if (options.Apply)
    {
        ReplaceAtomically(acceptedDirectory, replacements);
    }

    var audit = JsonSerializer.SerializeToElement(new
    {
        schema = "ledger-direct-fix-audit-v1",
        mode = options.Apply ? "apply" : options.ExpectClean ? "fixed-point-check" : "enumerate",
        candidate_lean_report = Path.GetRelativePath(repositoryRoot, reportPath).Replace(Path.DirectorySeparatorChar, '/'),
        accepted_events = events.Length,
        stale_events = stale.Length,
        stale_edges = staleEdges,
        cascade_members_within_stale_set = cascadeMembers.Length,
        additional_cascade_events = 0,
        expected_only_shards = expectedOnly,
        actual_only_shards = actualOnly,
        stale_event_shards = actualShardPaths,
        cascade_member_modules = cascadeMembers,
        rewrites = replacements.Select(static item => new
        {
            module = item.Source.DescriptorSelector,
            deleted = item.Source.RepoRelativePath,
            created = $"{AcceptedRoot}/{item.FileName}",
            stale_prerequisites = item.StaleRecordedPrerequisites,
            active_prerequisites = item.ActivePrerequisites,
        }),
    });
    WriteAudit(options.AuditOut, audit);
    Console.WriteLine(
        $"LEDGER_DIRECT_FIX mode={(options.Apply ? "apply" : options.ExpectClean ? "fixed-point-check" : "enumerate")} "
        + $"accepted_events={events.Length} stale_events={stale.Length} stale_edges={staleEdges} "
        + $"cascade_members={cascadeMembers.Length} additional_cascade_events=0 "
        + $"created={(options.Apply ? replacements.Length : 0)} deleted={(options.Apply ? replacements.Length : 0)}");
    return 0;
}
catch (Exception exception)
{
    Console.Error.WriteLine($"LEDGER_DIRECT_FIX_FAILED {exception.Message}");
    return 1;
}

static LeanReport ReadReport(string path)
{
    using var document = JsonDocument.Parse(File.ReadAllBytes(path));
    var root = document.RootElement;
    if (RequiredString(root, "schema") != "stratalint-raw-lean-report-v2")
    {
        throw new FormatException("Candidate Lean report has the wrong schema.");
    }

    var modules = root.GetProperty("modules").EnumerateArray().Select(module => new LeanModule(
        RequiredString(module, "module"),
        RequiredString(module, "source_path"),
        module.GetProperty("imports").EnumerateArray()
            .Select(static item => item.GetString() ?? throw new FormatException("Lean import is not a string."))
            .ToImmutableArray())).ToImmutableArray();
    return new LeanReport(modules);
}

static ImmutableArray<FreezeEvent> ReadEvents(string directory)
{
    var events = ImmutableArray.CreateBuilder<FreezeEvent>();
    foreach (var path in Directory.EnumerateFiles(directory, "*.json").Order(StringComparer.Ordinal))
    {
        var bytes = File.ReadAllBytes(path);
        using var document = JsonDocument.Parse(bytes);
        var root = document.RootElement;
        if (RequiredString(root, "event_type") != "Freeze"
            || root.GetProperty("schema_version").GetInt32() != 5)
        {
            throw new FormatException($"{path} is not a schema-v5 Freeze event.");
        }

        var canonicalBytes = StructuredCanonicalWriter.WriteJson(root);
        if (!canonicalBytes.AsSpan().SequenceEqual(bytes))
        {
            throw new FormatException($"{path} is not canonical JSON.");
        }

        var eventHash = RequiredString(root, "event_hash");
        if (!string.Equals(Path.GetFileNameWithoutExtension(path), eventHash["sha256:".Length..], StringComparison.Ordinal))
        {
            throw new FormatException($"{path} is not named by its event_hash.");
        }

        var payload = root.GetProperty("payload").Clone();
        var prerequisites = RequiredStrings(payload, "prerequisite_frozen_node_ids");
        events.Add(new FreezeEvent(
            path,
            $"{AcceptedRoot}/{Path.GetFileName(path)}",
            payload,
            RequiredString(payload, "descriptor_selector"),
            RequiredString(payload, "statement_id"),
            prerequisites));
    }

    return events.ToImmutable();
}

static ImmutableArray<string> ManagedDependencies(
    LeanModule module,
    IReadOnlyDictionary<string, string> modulePaths,
    IReadOnlyDictionary<string, FreezeEvent> eventsByPath)
{
    var result = ImmutableArray.CreateBuilder<string>();
    foreach (var import in module.Imports.Distinct(StringComparer.Ordinal))
    {
        if (!modulePaths.TryGetValue(import, out var path) || !path.StartsWith("D5/", StringComparison.Ordinal))
        {
            continue;
        }

        if (!eventsByPath.ContainsKey(path))
        {
            throw new FormatException($"Closed module {module.SourcePath} imports non-frozen managed module {path}.");
        }

        result.Add(path);
    }

    return result.Order(StringComparer.Ordinal).ToImmutableArray();
}

static ImmutableDictionary<string, CanonicalNode> ComputeCanonicalNodes(
    IReadOnlyDictionary<string, FreezeEvent> events,
    IReadOnlyDictionary<string, ImmutableArray<string>> dependencies)
{
    var result = new Dictionary<string, CanonicalNode>(StringComparer.Ordinal);
    var visiting = new HashSet<string>(StringComparer.Ordinal);
    foreach (var path in events.Keys.Order(StringComparer.Ordinal))
    {
        Visit(path);
    }

    return result.ToImmutableDictionary(StringComparer.Ordinal);

    void Visit(string path)
    {
        if (result.ContainsKey(path))
        {
            return;
        }

        if (!visiting.Add(path))
        {
            throw new FormatException($"Managed Lean import cycle reaches {path}.");
        }

        foreach (var dependency in dependencies[path])
        {
            Visit(dependency);
        }

        var prerequisites = dependencies[path]
            .Select(dependency => result[dependency].FrozenNodeId)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var frozenNodeId = CanonicalBridge.ComputeFrozenNodeId(path, events[path].StatementId, prerequisites);
        result.Add(path, new CanonicalNode(frozenNodeId, prerequisites));
        visiting.Remove(path);
    }
}

static Replacement BuildReplacement(StaleEvent stale, CanonicalNode canonical)
{
    var payload = JsonNode.Parse(stale.Event.Payload.GetRawText())?.AsObject()
        ?? throw new FormatException("Freeze payload is not a JSON object.");
    payload["prerequisite_frozen_node_ids"] = new JsonArray(
        canonical.Prerequisites.Select(static item => JsonValue.Create(item)).ToArray());
    var payloadElement = JsonSerializer.SerializeToElement(payload);
    var encoded = CanonicalBridge.WriteFreeze(payloadElement);
    var repoPath = $"{AcceptedRoot}/{encoded.Hash["sha256:".Length..]}.json";
    var snapshot = SnapshotDecoder.Decode(RawRepositorySnapshot.Create([
        new RawRepositoryEntry(repoPath, encoded.Bytes),
    ])) as SnapshotDecodeOutcome.Decoded
        ?? throw new FormatException("Canonical replacement could not be decoded as a repository file.");
    var loaded = FrozenAcceptedEventLoader.LoadFiles(snapshot.Snapshot.Files.Values);
    if (loaded is DagLedgerFilesLoadOutcome.Invalid invalid)
    {
        throw new FormatException("Canonical writer emitted an invalid replacement: " + invalid.Message);
    }

    return new Replacement(
        stale.Event,
        encoded.Hash["sha256:".Length..] + ".json",
        encoded.Bytes,
        stale.StaleRecordedPrerequisites,
        stale.ActivePrerequisites);
}

static void ValidateReplacementSet(
    ImmutableArray<FreezeEvent> events,
    ImmutableArray<Replacement> replacements,
    ImmutableDictionary<string, CanonicalNode> canonical)
{
    if (replacements.Select(static item => item.FileName).Distinct(StringComparer.Ordinal).Count() != replacements.Length)
    {
        throw new FormatException("Replacement set contains duplicate content-addressed file names.");
    }

    var deleted = replacements.Select(static item => Path.GetFileName(item.Source.FullPath)).ToImmutableHashSet(StringComparer.Ordinal);
    var retained = events.Select(static item => Path.GetFileName(item.FullPath)).Where(path => !deleted.Contains(path))
        .ToImmutableHashSet(StringComparer.Ordinal);
    if (replacements.Any(item => retained.Contains(item.FileName)
            || string.Equals(item.FileName, Path.GetFileName(item.Source.FullPath), StringComparison.Ordinal)))
    {
        throw new FormatException("Replacement set collides with a retained or stale shard path.");
    }

    var identities = canonical.Values.Select(static item => item.FrozenNodeId).ToImmutableHashSet(StringComparer.Ordinal);
    if (identities.Count != canonical.Count
        || canonical.Values.SelectMany(static item => item.Prerequisites).Any(prerequisite => !identities.Contains(prerequisite)))
    {
        throw new FormatException("Canonical replacement graph is not a closed DAG with unique identities.");
    }
}

static void ReplaceAtomically(string acceptedDirectory, ImmutableArray<Replacement> replacements)
{
    if (replacements.IsEmpty)
    {
        return;
    }

    var stagingDirectory = Path.Combine(acceptedDirectory, $".ledger-direct-fix-{Guid.NewGuid():N}");
    var newDirectory = Path.Combine(stagingDirectory, "new");
    var oldDirectory = Path.Combine(stagingDirectory, "old");
    var published = new Stack<string>();
    var displaced = new Stack<(string Staged, string Original)>();
    try
    {
        Directory.CreateDirectory(newDirectory);
        Directory.CreateDirectory(oldDirectory);
        foreach (var replacement in replacements)
        {
            var path = Path.Combine(newDirectory, replacement.FileName);
            using var stream = new FileStream(path, FileMode.CreateNew, FileAccess.Write, FileShare.None);
            stream.Write(replacement.Bytes.AsSpan());
            stream.Flush(flushToDisk: true);
        }

        foreach (var replacement in replacements)
        {
            var staged = Path.Combine(oldDirectory, Path.GetFileName(replacement.Source.FullPath));
            File.Move(replacement.Source.FullPath, staged);
            displaced.Push((staged, replacement.Source.FullPath));
        }

        foreach (var replacement in replacements)
        {
            var staged = Path.Combine(newDirectory, replacement.FileName);
            var final = Path.Combine(acceptedDirectory, replacement.FileName);
            File.Move(staged, final);
            published.Push(final);
        }

        Directory.Delete(stagingDirectory, recursive: true);
    }
    catch
    {
        while (published.TryPop(out var path))
        {
            if (File.Exists(path))
            {
                File.Delete(path);
            }
        }

        while (displaced.TryPop(out var item))
        {
            if (File.Exists(item.Staged))
            {
                File.Move(item.Staged, item.Original);
            }
        }

        if (Directory.Exists(stagingDirectory))
        {
            Directory.Delete(stagingDirectory, recursive: true);
        }

        throw;
    }
}

static ImmutableArray<string> ReadExpectedShardPaths(string path)
{
    using var document = JsonDocument.Parse(File.ReadAllBytes(path));
    return document.RootElement.EnumerateArray()
        .Select(static item => RequiredString(item, "event_shard"))
        .Distinct(StringComparer.Ordinal)
        .Order(StringComparer.Ordinal)
        .ToImmutableArray();
}

static void WriteAudit(string path, JsonElement audit)
{
    var fullPath = Path.GetFullPath(path);
    Directory.CreateDirectory(Path.GetDirectoryName(fullPath)
        ?? throw new InvalidOperationException("Audit path has no parent directory."));
    var bytes = StructuredCanonicalWriter.WriteJson(audit);
    var temporary = fullPath + ".tmp";
    File.WriteAllBytes(temporary, bytes.AsSpan());
    File.Move(temporary, fullPath, overwrite: true);
}

static string RequiredString(JsonElement value, string property)
{
    if (!value.TryGetProperty(property, out var item) || item.ValueKind != JsonValueKind.String)
    {
        throw new FormatException($"JSON property {property} is missing or is not a string.");
    }

    return item.GetString()!;
}

static ImmutableArray<string> RequiredStrings(JsonElement value, string property)
{
    if (!value.TryGetProperty(property, out var item) || item.ValueKind != JsonValueKind.Array)
    {
        throw new FormatException($"JSON property {property} is missing or is not an array.");
    }

    return item.EnumerateArray()
        .Select(child => child.GetString() ?? throw new FormatException($"JSON array {property} contains a non-string."))
        .ToImmutableArray();
}

internal sealed record Options(
    string RepositoryRoot,
    string CandidateLeanReport,
    string AuditOut,
    string? ExpectedEnumeration,
    bool Apply,
    bool ExpectClean)
{
    internal static Options Parse(string[] arguments)
    {
        string? repositoryRoot = null;
        string? candidateLeanReport = null;
        string? auditOut = null;
        string? expectedEnumeration = null;
        var apply = false;
        var expectClean = false;
        for (var index = 0; index < arguments.Length; index++)
        {
            switch (arguments[index])
            {
                case "--repository-root":
                    repositoryRoot = Next(arguments, ref index);
                    break;
                case "--candidate-lean-report":
                    candidateLeanReport = Next(arguments, ref index);
                    break;
                case "--audit-out":
                    auditOut = Next(arguments, ref index);
                    break;
                case "--expected-enumeration":
                    expectedEnumeration = Next(arguments, ref index);
                    break;
                case "--apply":
                    apply = true;
                    break;
                case "--expect-clean":
                    expectClean = true;
                    break;
                default:
                    throw new ArgumentException($"Unknown argument {arguments[index]}.");
            }
        }

        if (repositoryRoot is null || candidateLeanReport is null || auditOut is null || apply && expectClean)
        {
            throw new ArgumentException(
                "USAGE: LedgerDirectFix --repository-root DIR --candidate-lean-report FILE --audit-out FILE "
                + "[--expected-enumeration FILE] [--apply|--expect-clean]");
        }

        if (!expectClean && expectedEnumeration is null)
        {
            throw new ArgumentException("Initial enumeration and apply require --expected-enumeration.");
        }

        return new Options(
            repositoryRoot,
            candidateLeanReport,
            auditOut,
            expectedEnumeration,
            apply,
            expectClean);
    }

    private static string Next(string[] arguments, ref int index)
    {
        index++;
        return index < arguments.Length && !string.IsNullOrWhiteSpace(arguments[index])
            ? arguments[index]
            : throw new ArgumentException("Option value is missing.");
    }
}

internal static class CanonicalBridge
{
    private const BindingFlags InternalStatic = BindingFlags.NonPublic | BindingFlags.Static;
    private static readonly MethodInfo StatementCreate = RequiredMethod(typeof(StatementId), "Create");
    private static readonly MethodInfo FrozenNodeCreate = RequiredMethod(typeof(FrozenNodeId), "Create");
    private static readonly MethodInfo ComputeNode = RequiredMethod(typeof(FrozenContentAddress), "ComputeFrozenNodeId");
    private static readonly MethodInfo WriteEvent = typeof(FrozenContentAddress).Assembly
        .GetType("StrataLint.Engine.FrozenLedgerCanonicalWriter", throwOnError: true)!
        .GetMethod("WriteDagEvent", InternalStatic)
        ?? throw new MissingMethodException("FrozenLedgerCanonicalWriter.WriteDagEvent");

    internal static string ComputeFrozenNodeId(
        string path,
        string statementId,
        ImmutableArray<string> prerequisites)
    {
        var statement = StatementCreate.Invoke(null, [statementId])!;
        var nodes = prerequisites.Select(item => (FrozenNodeId)FrozenNodeCreate.Invoke(null, [item])!).ToImmutableArray();
        var repoPath = RepoPath.TryCreate(path, out var parsed)
            ? parsed
            : throw new FormatException($"Invalid repository path {path}.");
        var result = ComputeNode.Invoke(null, [repoPath, statement, nodes]) as FrozenNodeId;
        return result?.Value ?? throw new InvalidOperationException("Canonical node writer returned no identity.");
    }

    internal static EncodedFreeze WriteFreeze(JsonElement payload)
    {
        var tuple = WriteEvent.Invoke(null, ["Freeze", payload, null])
            ?? throw new InvalidOperationException("Canonical event writer returned no value.");
        var tupleType = tuple.GetType();
        var bytes = (ImmutableArray<byte>)(tupleType.GetField("Item1")?.GetValue(tuple)
            ?? throw new MissingFieldException("Canonical writer result Item1"));
        var hash = (string)(tupleType.GetField("Item2")?.GetValue(tuple)
            ?? throw new MissingFieldException("Canonical writer result Item2"));
        return new EncodedFreeze(bytes, hash);
    }

    private static MethodInfo RequiredMethod(Type type, string name) =>
        type.GetMethod(name, InternalStatic)
        ?? throw new MissingMethodException(type.FullName, name);
}

internal sealed record LeanReport(ImmutableArray<LeanModule> Modules);

internal sealed record LeanModule(string Module, string SourcePath, ImmutableArray<string> Imports);

internal sealed record FreezeEvent(
    string FullPath,
    string RepoRelativePath,
    JsonElement Payload,
    string DescriptorSelector,
    string StatementId,
    ImmutableArray<string> RecordedPrerequisites);

internal sealed record CanonicalNode(string FrozenNodeId, ImmutableArray<string> Prerequisites);

internal sealed record EncodedFreeze(ImmutableArray<byte> Bytes, string Hash);

internal sealed record Replacement(
    FreezeEvent Source,
    string FileName,
    ImmutableArray<byte> Bytes,
    ImmutableArray<string> StaleRecordedPrerequisites,
    ImmutableArray<string> ActivePrerequisites);

internal sealed record StaleEvent(
    FreezeEvent Event,
    ImmutableArray<string> StaleRecordedPrerequisites,
    ImmutableArray<string> ActivePrerequisites)
{
    internal int StaleEdgeCount => ActivePrerequisites.Length;

    internal static StaleEvent Create(FreezeEvent @event, ImmutableArray<string> desired)
    {
        var stale = @event.RecordedPrerequisites.Except(desired, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var active = desired.Except(@event.RecordedPrerequisites, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        if (stale.Length != active.Length)
        {
            throw new FormatException(
                $"Freeze {@event.DescriptorSelector} changed prerequisite arity instead of identities.");
        }

        return new StaleEvent(@event, stale, active);
    }
}

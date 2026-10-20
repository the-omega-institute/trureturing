using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace StrataLint.Engine;

internal static class DigestionContextPointerStore
{
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = false,
        PropertyNamingPolicy = null,
        DefaultIgnoreCondition = JsonIgnoreCondition.Never,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        RespectRequiredConstructorParameters = true,
    };

    internal static bool IsCanonicalPath(string path)
    {
        if (!path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)) return false;
        var parts = path[BackfillInventoryLoader.RootPath.Length..].Split('/');
        return parts.Length == 3 && parts[1] == "context" && parts[2].EndsWith(".json", StringComparison.Ordinal)
            && DigestionNonpropositional.IsAtomId(parts[2][..^5]);
    }

    internal static ImmutableArray<DigestionContextPointerIndex> Load(
        RepositorySnapshot snapshot, string sourceId, string atomId)
    {
        var path = DigestionContextPointerIndex.RelativePath(sourceId, atomId);
        if (!snapshot.TryGetFile(path, out var file))
            throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING,
                $"CONTEXT_UNAVAILABLE atom_id={atomId}; run migrate-atom-context explicitly");
        return ParseVersions(file.RawBytes, sourceId, atomId);
    }

    internal static ImmutableArray<DigestionContextPointerIndex> ParseVersions(
        ImmutableArray<byte> bytes, string sourceId, string atomId)
    {
        try
        {
            using var json = JsonDocument.Parse(bytes.AsMemory());
            if (json.RootElement.ValueKind != JsonValueKind.Array)
                throw new FormatException("context versions must be an array");
            RejectDuplicateProperties(json.RootElement);
            var versions = json.RootElement.EnumerateArray().Select(item =>
                Parse([.. System.Text.Encoding.UTF8.GetBytes(item.GetRawText())])).ToImmutableArray();
            if (versions.IsEmpty || !versions.Select(index => index.VersionKey).SequenceEqual(
                    versions.Select(index => index.VersionKey).Order(StringComparer.Ordinal))
                || versions.Any(index => index.SourceId != sourceId
                    || index.Entries.Length != 1 || index.Entries[0].AtomId != atomId)
                || versions.Select(index => index.VersionKey).Distinct(StringComparer.Ordinal).Count() != versions.Length)
                throw new FormatException("context versions identity mismatch or ambiguity");
            return versions;
        }
        catch (JsonException error) { throw new FormatException("invalid context versions", error); }
    }

    private static void RejectDuplicateProperties(JsonElement element)
    {
        if (element.ValueKind == JsonValueKind.Object)
        {
            var names = new HashSet<string>(StringComparer.Ordinal);
            foreach (var property in element.EnumerateObject())
            {
                if (!names.Add(property.Name)) throw new FormatException("duplicate context property: " + property.Name);
                RejectDuplicateProperties(property.Value);
            }
        }
        else if (element.ValueKind == JsonValueKind.Array)
            foreach (var item in element.EnumerateArray()) RejectDuplicateProperties(item);
    }

    internal static DigestionContextOccurrence? Follow(RepositorySnapshot snapshot,
        DigestionContextPointerIndex index, DigestionContextOccurrence occurrence, bool next)
    {
        var id = next ? occurrence.NextAtomId : occurrence.PreviousAtomId;
        var start = next ? occurrence.NextStartByte : occurrence.PreviousStartByte;
        if (id is null) return null;
        var version = Load(snapshot, index.SourceId, id).SingleOrDefault(item => item.VersionKey == index.VersionKey)
            ?? throw new FormatException($"CONTEXT_VERSION_MISSING atom_id={id}");
        return version.Entries[0].Occurrences.SingleOrDefault(item => item.StartByte == start)
            ?? throw new FormatException($"CONTEXT_REFERENCE_MISSING atom_id={id}");
    }

    internal static ImmutableArray<byte> WriteVersions(IEnumerable<DigestionContextPointerIndex> versions)
    {
        var text = "[" + string.Join(",", versions.OrderBy(index => index.VersionKey, StringComparer.Ordinal)
            .Select(index => System.Text.Encoding.UTF8.GetString(Write(index).AsSpan()).TrimEnd())) + "]\n";
        return [.. System.Text.Encoding.UTF8.GetBytes(text)];
    }

    // The graph key identifies the writer's observation of the actual child chains.
    // It keeps two graph observations over identical prose from sharing pointers.
    internal static DigestionContextPointerIndex PreserveSavedGraph(RawRepositorySnapshot raw, DigestionContextPointerIndex index)
    {
        if (index.GraphSha256 is not null) return index;
        var files = raw.Entries.ToDictionary(file => file.Path, StringComparer.Ordinal);
        var different = false;
        foreach (var entry in index.Entries)
        {
            if (!files.TryGetValue(DigestionContextPointerIndex.RelativePath(index.SourceId, entry.AtomId), out var file)) continue;
            var saved = ParseVersions(file.Bytes, index.SourceId, entry.AtomId)
                .SingleOrDefault(version => version.SourceSha256 == index.SourceSha256 && version.GraphSha256 is null);
            if (saved is null) continue;
            if (saved.SourcePath != index.SourcePath || saved.Atomizer != index.Atomizer)
                throw new FormatException($"CONTEXT_VERSION_CONFLICT source_id={index.SourceId} atom_id={entry.AtomId}");
            different |= !Write(saved).AsSpan().SequenceEqual(Write(index with { Entries = [entry] }).AsSpan());
        }
        return different ? index with { GraphSha256 = DigestionFingerprint.ComputeOpaque(Write(index).AsSpan()).RawSha256 } : index;
    }

    internal static RawRepositorySnapshot Add(RawRepositorySnapshot raw, DigestionContextPointerIndex index)
    {
        var files = raw.Entries.ToDictionary(entry => entry.Path, StringComparer.Ordinal);
        foreach (var entry in index.Entries)
        {
            var path = DigestionContextPointerIndex.RelativePath(index.SourceId, entry.AtomId);
            var versions = files.TryGetValue(path, out var old)
                ? ParseVersions(old.Bytes, index.SourceId, entry.AtomId) : [];
            files[path] = new RawRepositoryEntry(path, WriteVersions(versions
                .Where(version => version.VersionKey != index.VersionKey)
                .Append(index with { Entries = [entry] })));
        }
        return RawRepositorySnapshot.Create(files.Values);
    }

    internal static ImmutableArray<byte> Write(DigestionContextPointerIndex index)
    {
        ArgumentNullException.ThrowIfNull(index);
        Validate(index);
        var dto = new ContextIndexDto(
            index.GraphSha256 is null ? DigestionContextPointerIndex.SchemaVersion : 2,
            index.SourceId,
            index.SourcePath,
            index.Atomizer,
            index.SourceSha256,
            index.Entries.Select(static entry => new ContextEntryDto(
                entry.AtomId,
                entry.Occurrences.Select(static occurrence => new ContextOccurrenceDto(
                    occurrence.OccurrenceIndex,
                    occurrence.StreamIndex,
                    occurrence.StreamCount,
                    occurrence.PreviousAtomId,
                    occurrence.NextAtomId,
                    occurrence.StartByte,
                    occurrence.EndByte,
                    occurrence.PreviousStartByte,
                    occurrence.NextStartByte,
                    occurrence.GoverningContext.Select(static scope =>
                        new ContextScopeDto(scope.Relation, scope.AtomId)).ToArray())).ToArray())).ToArray())
        { GraphSha256 = index.GraphSha256 };
        return [.. JsonSerializer.SerializeToUtf8Bytes(dto, JsonOptions), (byte)'\n'];
    }

    internal static DigestionContextPointerIndex Parse(ImmutableArray<byte> bytes)
    {
        try
        {
            using var json = JsonDocument.Parse(bytes.AsMemory());
            RejectDuplicateProperties(json.RootElement);
            var dto = JsonSerializer.Deserialize<ContextIndexDto>(bytes.AsSpan(), JsonOptions)
                ?? throw new FormatException("context index is empty");
            if (dto.SchemaVersion is not (1 or 2))
                throw new FormatException("unsupported context index schema_version");
            if (dto.SchemaVersion == 1 && json.RootElement.TryGetProperty("GraphSha256", out _)
                || dto.SchemaVersion == 2 && dto.GraphSha256 is null)
                throw new FormatException("context graph identity does not match schema_version");
            var entries = dto.Entries.Select(entry => new DigestionContextPointerEntry(
                entry.AtomId,
                entry.Occurrences.Select(occurrence => new DigestionContextOccurrence(
                    occurrence.OccurrenceIndex,
                    occurrence.StreamIndex,
                    occurrence.StreamCount,
                    occurrence.PreviousAtomId,
                    occurrence.NextAtomId,
                    occurrence.StartByte,
                    occurrence.EndByte,
                    occurrence.PreviousStartByte,
                    occurrence.NextStartByte,
                    occurrence.GoverningContext.Select(scope =>
                        new DigestionContextScopePointer(scope.Relation, scope.AtomId)).ToImmutableArray())).ToImmutableArray()))
                .ToImmutableArray();
            var index = new DigestionContextPointerIndex(
                dto.SourceId, dto.SourcePath, dto.Atomizer, dto.SourceSha256, entries) { GraphSha256 = dto.GraphSha256 };
            Validate(index);
            return index;
        }
        catch (Exception error) when (error is JsonException or NullReferenceException or ArgumentNullException)
        {
            throw new FormatException("context index is not canonical JSON", error);
        }
    }

    internal static void Validate(DigestionContextPointerIndex index)
    {
        if (string.IsNullOrWhiteSpace(index.SourceId)
            || string.IsNullOrWhiteSpace(index.SourcePath)
            || string.IsNullOrWhiteSpace(index.Atomizer)
            || !DigestionFingerprint.IsCanonicalSha256(index.SourceSha256)
            || index.GraphSha256 is not null && !DigestionFingerprint.IsCanonicalSha256(index.GraphSha256))
            throw new FormatException("context index has invalid source identity");

        var ordered = index.Entries.OrderBy(static entry => entry.AtomId, StringComparer.Ordinal).ToImmutableArray();
        if (!index.Entries.SequenceEqual(ordered)
            || index.Entries.Any(entry => !DigestionNonpropositional.IsAtomId(entry.AtomId))
            || index.Entries.Select(entry => entry.AtomId).Distinct(StringComparer.Ordinal).Count() != index.Entries.Length)
            throw new FormatException("context index entries must be sorted canonical atom ids");
        foreach (var entry in index.Entries)
        {
            if (entry.Occurrences.Select(item => item.StartByte).Distinct().Count() != entry.Occurrences.Length)
                throw new FormatException("duplicate context occurrence");
            if (entry.Occurrences.IsEmpty
                || !entry.Occurrences.Select(static occurrence => occurrence.OccurrenceIndex)
                    .SequenceEqual(entry.Occurrences.Select(static occurrence => occurrence.OccurrenceIndex).Order()))
                throw new FormatException($"context index occurrences are not ordered: {entry.AtomId}");
            foreach (var occurrence in entry.Occurrences)
            {
                if (occurrence.OccurrenceIndex < 1 || occurrence.StreamIndex < 1
                    || occurrence.StreamCount < occurrence.StreamIndex
                    || occurrence.PreviousAtomId is not null && !DigestionNonpropositional.IsAtomId(occurrence.PreviousAtomId)
                    || occurrence.NextAtomId is not null && !DigestionNonpropositional.IsAtomId(occurrence.NextAtomId)
                    || (occurrence.PreviousAtomId is null) != (occurrence.PreviousStartByte is null)
                    || (occurrence.NextAtomId is null) != (occurrence.NextStartByte is null)
                    || occurrence.StartByte < 0 || occurrence.EndByte <= occurrence.StartByte
                    || occurrence.PreviousStartByte is < 0 || occurrence.NextStartByte is < 0
                    || (occurrence.PreviousAtomId is null) != (occurrence.StreamIndex == 1)
                    || (occurrence.NextAtomId is null) != (occurrence.StreamIndex == occurrence.StreamCount)
                    || occurrence.GoverningContext.Any(scope =>
                        string.IsNullOrWhiteSpace(scope.Relation)
                        || !DigestionNonpropositional.IsAtomId(scope.AtomId)))
                    throw new FormatException($"context index occurrence is invalid: {entry.AtomId}");
            }
        }
    }

    private sealed record ContextIndexDto(
        int SchemaVersion,
        string SourceId,
        string SourcePath,
        string Atomizer,
        string SourceSha256,
        ContextEntryDto[] Entries)
    {
        [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
        public string? GraphSha256 { get; init; }
    }

    private sealed record ContextEntryDto(string AtomId, ContextOccurrenceDto[] Occurrences);

    private sealed record ContextOccurrenceDto(
        int OccurrenceIndex,
        int StreamIndex,
        int StreamCount,
        string? PreviousAtomId,
        string? NextAtomId,
        int StartByte,
        int EndByte,
        int? PreviousStartByte,
        int? NextStartByte,
        ContextScopeDto[] GoverningContext);

    private sealed record ContextScopeDto(string Relation, string AtomId);
}


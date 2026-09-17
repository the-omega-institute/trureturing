using System.Collections.Immutable;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

// Expands the existing registered path sets. The JSON manifest remains the
// authority for runtime support; the historical overlay contract is shared
// with the admission reader, independently of executable transport.
internal sealed class InformationTemplateHistoryInputs
{
    internal ImmutableArray<RawRepositoryEntry> ProducerFiles { get; }
    internal string Producer { get; }
    internal ImmutableArray<InformationTemplateProducerRecord> Records { get; }
    private readonly RawRepositorySnapshot candidate;

    internal InformationTemplateHistoryInputs(RawRepositorySnapshot candidate)
    {
        this.candidate = candidate;
        var authored = candidate.Entries.Where(e => e.IsTracked).ToDictionary(e => e.Path, StringComparer.Ordinal);
        var selected = Select(authored, "lean-report").Concat(Select(authored, "inspector_sources"))
            .Concat(Select(authored, "config_inputs")).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        foreach (var path in authored.Keys.Where(InformationTemplateEvidence.ProducerInput))
            if (!selected.Contains(path, StringComparer.Ordinal))
                throw new FormatException("history producer overlay input is not registered: " + path);
        ProducerFiles = selected.Select(p => Plain(authored[p])).ToImmutableArray();
        var records = ProducerFiles.Select(e => new InformationTemplateProducerRecord(e.Path, e.GitMode,
            InformationTemplateJson.Sha256(e.Bytes.AsSpan()))).ToList();
        using var manifest = Manifest(authored);
        foreach (var set in new[] { manifest.RootElement.GetProperty("config_inputs"),
            manifest.RootElement.GetProperty("producer_scopes").GetProperty("lean-report") })
        foreach (var item in set.GetProperty("include").EnumerateArray())
        {
            var path = InformationTemplateJson.String(item, "pattern");
            if (item.GetProperty("optional").GetBoolean() && !path.Contains('*') && !authored.ContainsKey(path))
                records.Add(new(path, "absent", null));
        }
        Records = records.Distinct().OrderBy(r => r.Path, StringComparer.Ordinal).ToImmutableArray();
        Producer = InformationTemplateJson.Sha256(InformationTemplateHistoryPlan.ProducerBytes(Records).AsSpan());
    }

    internal (RepositorySnapshot Hybrid, ImmutableArray<RawRepositoryEntry> Files) Material(string revision,
        RawRepositorySnapshot historical)
    {
        InformationTemplateJson.Hash(revision, 40);
        // H does not overlay this executable configuration. Executing either
        // version would silently invent a different evidence contract.
        if (historical.Entries.Concat(candidate.Entries).Any(e => e.Path == "lakefile.lean"))
            throw new FormatException("history unsupported executable input outside H overlay: lakefile.lean");
        var current = Decode(candidate);
        var hybrid = InformationTemplateEvidence.HistoricalInputs(Decode(historical), current);
        var files = historical.Entries.Where(e => IsContent(e.Path)).Select(Plain)
            .Concat(ProducerFiles).OrderBy(e => e.Path, StringComparer.Ordinal).ToImmutableArray();
        var written = files.ToDictionary(e => e.Path, StringComparer.Ordinal);
        var all = hybrid.Files.Values.ToDictionary(f => f.Path.Value,
            f => new RawRepositoryEntry(f.Path.Value, f.RawBytes), StringComparer.Ordinal);
        foreach (var path in Select(all, "report_modules").Concat(Select(all, "config_inputs"))
            .Concat(Select(all, "dependency_sources")).Distinct(StringComparer.Ordinal))
            if (!written.TryGetValue(path, out var file) || !file.Bytes.AsSpan().SequenceEqual(all[path].Bytes.AsSpan()))
                throw new FormatException("history unsupported or unequal H execution input: " + path);
        return (hybrid, files);
    }

    private static bool IsContent(string path) => path == "Trureturing.lean"
        || path.StartsWith("D5/", StringComparison.Ordinal) && path.EndsWith(".lean", StringComparison.Ordinal)
        || path.StartsWith("Golden/Frozen/state/", StringComparison.Ordinal);

    internal static RawRepositoryEntry Plain(RawRepositoryEntry entry)
    {
        if (!RepoPath.TryCreate(entry.Path, out _) || entry.Path.Contains('\\')
            || entry.Path.Split('/').Any(p => p is "" or "." or ".." or ".git" or ".lake" or "bin" or "obj")
            || !entry.IsTracked || entry.GitMode is not ("100644" or "100755"))
            throw new FormatException("history requires a tracked regular authored input: " + entry.Path);
        return entry;
    }

    internal static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
        _ => throw new InvalidOperationException("snapshot decode failed"),
    };

    internal static JsonDocument Manifest(IReadOnlyDictionary<string, RawRepositoryEntry> files)
    {
        if (!files.TryGetValue("lean-report-inputs.json", out var file))
            throw new FormatException("history requires lean-report-inputs.json");
        using var source = JsonDocument.Parse(file.Bytes.AsMemory());
        // Canonicalization also detects duplicate JSON members, at every depth.
        var bytes = InformationTemplateJson.Canonical(source.RootElement);
        var document = JsonDocument.Parse(bytes.AsMemory());
        if (document.RootElement.GetProperty("schema_version").GetRawText() != "1"
            || !document.RootElement.GetProperty("report_semantic_version").TryGetInt32(out var version) || version <= 0)
        {
            document.Dispose();
            throw new FormatException("history input manifest has unsupported schema/version");
        }
        return document;
    }

    internal static ImmutableArray<string> Select(IReadOnlyDictionary<string, RawRepositoryEntry> files, string name)
    {
        using var manifest = Manifest(files);
        var value = name == "lean-report" ? manifest.RootElement.GetProperty("producer_scopes").GetProperty(name)
            : manifest.RootElement.GetProperty(name);
        InformationTemplateJson.Fields(value, "include", "exclude");
        var excludes = value.GetProperty("exclude").EnumerateArray().Select(e => FileMapGlob.Create(e.GetString()!)).ToArray();
        var result = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var item in value.GetProperty("include").EnumerateArray())
        {
            InformationTemplateJson.Fields(item, "pattern", "optional");
            var pattern = FileMapGlob.Create(InformationTemplateJson.String(item, "pattern"));
            var matches = files.Keys.Where(p => pattern.IsMatch(p) && !excludes.Any(e => e.IsMatch(p))).ToArray();
            if (matches.Length == 0 && !item.GetProperty("optional").GetBoolean())
                throw new FormatException("history required registered input absent: " + pattern.Pattern);
            foreach (var path in matches) { Plain(files[path]); result.Add(path); }
        }
        return result.ToImmutableArray();
    }

    internal static InformationTemplateHistoryCoordinates Coordinates(RepositorySnapshot snapshot)
    {
        var files = snapshot.Files.Values.ToDictionary(f => f.Path.Value, f => new RawRepositoryEntry(f.Path.Value, f.RawBytes));
        using var manifest = Manifest(files);
        var version = manifest.RootElement.GetProperty("report_semantic_version").GetRawText();
        var producer = HashText($"schema=stratalint-lean-report-compatibility\nversion={version}\n");
        string InputHash(string name) => HashText(string.Concat(Select(files, name).Select(path =>
            InformationTemplateJson.Sha256(files[path].Bytes.AsSpan()) + "  " + path + "\n")));
        var sources = InputHash("report_modules");
        var config = InputHash("config_inputs");
        var common = $"repository_inspector_sha256={producer}\nlean_sources_sha256={sources}\nlean_config_sha256={config}\n";
        return new(producer, sources, config,
            HashText("schema=stratalint-lean-report-repository-input-v1\n" + common),
            HashText($"schema=stratalint-lean-report-input-v1\nproducer_sha256={producer}\n" + common));
    }

    private static string HashText(string text) => InformationTemplateJson.Sha256(Encoding.UTF8.GetBytes(text));
}

internal sealed record InformationTemplateHistoryCoordinates(string Compatibility, string Sources, string Config,
    string Repository, string Input);

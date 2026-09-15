using System.Collections.Immutable;
using System.Collections.Concurrent;
using System.Runtime.CompilerServices;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record InformationOccurrenceKey(
    string Root, string RegistrationModule, string Theorem, string ObjectArena, string Catalog);

internal sealed record InformationTemplateContentInput(string Path, string Sha256);

internal sealed record InformationTemplateDebtRow(
    InformationOccurrenceKey Key,
    string SeedBase,
    string StatementIdentity,
    string RegistrationSourceSha256,
    ImmutableArray<InformationTemplateContentInput> ContentInputs);

internal sealed record InformationTemplateActivation(string SeedBase, bool Activated);

internal static class InformationTemplateDebtStore
{
    public const string Root = "Golden/InformationTemplateDebt/";
    public const string ActivationPath = Root + "activation.json";

    // RepositorySnapshot and its files are immutable. Share only their parsed
    // link policy and byte digests; every wire record is still checked below.
    // A replacement snapshot gets an independent index, even for equal paths.
    private static readonly ConditionalWeakTable<RepositorySnapshot, InputIndex> InputIndices = new();

    private sealed class InputIndex(RepositorySnapshot snapshot)
    {
        private readonly ImmutableArray<FileMapSymlink> links =
            snapshot.TryGetFile(AdmissionPlanePolicy.FileMapPath, out var manifest)
                ? FileMapSymlinkPolicy.Parse(manifest.RawBytes.AsSpan(), AdmissionPlanePolicy.FileMapPath)
                : [];
        private readonly ConcurrentDictionary<string, string> hashes = new(StringComparer.Ordinal);

        internal bool Matches(string path, string digest) =>
            !links.Any(link => path == link.Path || path.StartsWith(link.Path + "/", StringComparison.Ordinal))
            && snapshot.TryGetFile(path, out var file)
            && hashes.GetOrAdd(path, _ => InformationTemplateJson.Sha256(file.RawBytes.AsSpan())) == digest;
    }

    public static string PathFor(InformationOccurrenceKey key)
    {
        var tuple = new[] { key.Root, key.RegistrationModule, key.Theorem, key.ObjectArena, key.Catalog };
        foreach (var name in tuple) InformationTemplateJson.Name(name);
        var json = InformationTemplateJson.Canonical(JsonSerializer.SerializeToElement(tuple), newline: false);
        var domain = Encoding.UTF8.GetBytes("DTR-occurrence-v1\0");
        var bytes = new byte[domain.Length + json.Length];
        domain.CopyTo(bytes, 0);
        json.AsSpan().CopyTo(bytes.AsSpan(domain.Length));
        return Root + InformationTemplateJson.Sha256(bytes) + ".json";
    }

    public static InformationTemplateDebtRow ReadRow(
        string path, ReadOnlySpan<byte> bytes, string authorizedSeed,
        RepositorySnapshot seedInputs)
    {
        using var doc = InformationTemplateJson.Read(bytes);
        var value = doc.RootElement;
        InformationTemplateJson.Fields(value, "schema_version", "key", "seed_base",
            "base_statement_identity", "base_registration_source_sha256", "base_content_inputs", "reason");
        InformationTemplateJson.Version(value);
        if (InformationTemplateJson.String(value, "reason") != "undeclared")
            throw new FormatException("DTR-DebtSchema: debt reason must be undeclared");
        var key = ReadKey(value.GetProperty("key"));
        if (path != PathFor(key)) throw new FormatException("DTR-DebtSchema: wrong key/filename");
        var seed = InformationTemplateJson.Hash(InformationTemplateJson.String(value, "seed_base"), 40);
        if (seed != InformationTemplateJson.Hash(authorizedSeed, 40))
            throw new FormatException("DTR-Seed: row retargets protected seed_base");
        var statement = InformationTemplateJson.Hash(InformationTemplateJson.String(value, "base_statement_identity"), 64);
        var source = InformationTemplateJson.Hash(InformationTemplateJson.String(value, "base_registration_source_sha256"), 64);
        var inputs = ReadInputs(value.GetProperty("base_content_inputs"), seedInputs);
        if (!inputs.Any(input => input.Sha256 == source))
            throw new FormatException("DTR-DebtSchema: registration source absent from content inputs");
        return new(key, seed, statement, source, inputs);
    }

    public static ImmutableArray<byte> WriteRow(InformationTemplateDebtRow row) =>
        InformationTemplateJson.Canonical(JsonSerializer.SerializeToElement(new
        {
            schema_version = 1,
            key = KeyJson(row.Key),
            seed_base = row.SeedBase,
            base_statement_identity = row.StatementIdentity,
            base_registration_source_sha256 = row.RegistrationSourceSha256,
            base_content_inputs = row.ContentInputs.Select(input => new { path = input.Path, sha256 = input.Sha256 }),
            reason = "undeclared",
        }));

    public static InformationTemplateActivation ReadActivation(RepositorySnapshot protectedBase)
    {
        if (!protectedBase.TryGetFile(ActivationPath, out var file))
            throw new FormatException("DTR-Activation: protected activation unavailable");
        using var doc = InformationTemplateJson.Read(file.RawBytes.AsSpan());
        var value = doc.RootElement;
        InformationTemplateJson.Fields(value, "schema_version", "seed_base", "activated");
        InformationTemplateJson.Version(value);
        var activated = value.GetProperty("activated");
        if (activated.ValueKind is not (JsonValueKind.True or JsonValueKind.False))
            throw new FormatException("DTR-Activation: activated must be Boolean");
        return new(InformationTemplateJson.Hash(InformationTemplateJson.String(value, "seed_base"), 40), activated.GetBoolean());
    }

    public static ImmutableArray<byte> WriteActivation(InformationTemplateActivation activation) =>
        InformationTemplateJson.Canonical(JsonSerializer.SerializeToElement(new
        {
            schema_version = 1, seed_base = InformationTemplateJson.Hash(activation.SeedBase, 40),
            activated = activation.Activated,
        }));

    internal static JsonElement KeyJson(InformationOccurrenceKey key) => JsonSerializer.SerializeToElement(new
    {
        root = key.Root, registration_module = key.RegistrationModule, theorem = key.Theorem,
        object_arena = key.ObjectArena, catalog = key.Catalog,
    });

    internal static InformationOccurrenceKey ReadKey(JsonElement value)
    {
        InformationTemplateJson.Fields(value, "root", "registration_module", "theorem", "object_arena", "catalog");
        string Name(string field) => InformationTemplateJson.Name(InformationTemplateJson.String(value, field));
        return new(Name("root"), Name("registration_module"), Name("theorem"), Name("object_arena"), Name("catalog"));
    }

    internal static ImmutableArray<InformationTemplateContentInput> ReadInputs(JsonElement value, RepositorySnapshot inputs)
    {
        if (value.ValueKind != JsonValueKind.Array || value.GetArrayLength() == 0)
            throw new FormatException("DTR-DebtSchema: nonempty content inputs required");
        var result = ImmutableArray.CreateBuilder<InformationTemplateContentInput>();
        var index = InputIndices.GetValue(inputs, static snapshot => new InputIndex(snapshot));
        string? previous = null;
        foreach (var item in value.EnumerateArray())
        {
            InformationTemplateJson.Fields(item, "path", "sha256");
            var path = InformationTemplateJson.String(item, "path");
            var sha256 = InformationTemplateJson.Hash(InformationTemplateJson.String(item, "sha256"), 64);
            if (!RepoPath.TryCreate(path, out _) || path.Contains('\\')
                || path.Split('/').Any(part => part is "" or "." or "..")
                || previous is not null && string.CompareOrdinal(previous, path) >= 0
                || !index.Matches(path, sha256))
                throw new FormatException($"DTR-DebtSchema: unavailable, changed or noncanonical input {path}");
            previous = path;
            result.Add(new(path, sha256));
        }

        return result.ToImmutable();
    }

    public static ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> Load(
        RepositorySnapshot snapshot, InformationTemplateActivation activation, RepositorySnapshot seedInputs)
    {
        var rows = ImmutableDictionary.CreateBuilder<InformationOccurrenceKey, InformationTemplateDebtRow>();
        foreach (var file in snapshot.Files.Values.Where(file => file.Path.Value.StartsWith(Root, StringComparison.Ordinal)
                     && file.Path.Value != ActivationPath))
        {
            var row = ReadRow(file.Path.Value, file.RawBytes.AsSpan(), activation.SeedBase, seedInputs);
            if (!rows.TryAdd(row.Key, row)) throw new FormatException("DTR-DebtSchema: duplicate logical key");
        }

        return rows.ToImmutable();
    }
}

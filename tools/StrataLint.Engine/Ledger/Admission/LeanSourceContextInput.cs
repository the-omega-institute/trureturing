using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record LeanSourceCommand(int Start, int End, string Kind, string Namespace,
    bool Equality, ImmutableArray<LeanSourceCommand> Children)
{
    internal bool EqualityAt(int offset) => Children.FirstOrDefault(child =>
        child.Start <= offset && offset < child.End)?.EqualityAt(offset) ?? Equality;
}

internal sealed record LeanSourceFileContext(int HeaderEnd, bool InitialEquality,
    ImmutableArray<LeanSourceCommand> Commands)
{
    internal bool EqualityAt(int offset) => Commands.FirstOrDefault(command =>
        command.Start <= offset && offset < command.End)?.EqualityAt(offset) ?? InitialEquality;
}

internal sealed record LeanSourceContextRequest(string Side, string Path, string Kind);

// Run-local input to source consumers. Loading does no Lean execution or I/O beyond
// the bundle bytes supplied by the CLI. Validation is at demand, so an unused row
// never turns a judge-only change or historical source into a rollout failure.
internal sealed class LeanSourceContextInput
{
    internal const string Schema = "lean-source-context/1";
    private readonly JsonElement? document;
    private readonly string? documentError;
    private readonly RepositorySnapshot? current;
    private readonly RepositorySnapshot? protectedBase;
    private readonly Dictionary<(RepositorySnapshot Snapshot, string Side, RepoPath Path), LeanSourceFileContext> files = [];
    private readonly HashSet<LeanSourceContextRequest> requests = [];
    private readonly List<string> malformed = [];
    internal IReadOnlyList<string> MalformedRows => malformed;

    private LeanSourceContextInput(JsonElement? document, RepositorySnapshot? current,
        RepositorySnapshot? protectedBase = null, string? documentError = null)
    { this.document = document; this.current = current; this.protectedBase = protectedBase;
        this.documentError = documentError; }

    internal static LeanSourceContextInput Empty => new(null, null);
    internal ImmutableArray<LeanSourceContextRequest> Requests => requests.OrderBy(r => r.Side,
        StringComparer.Ordinal).ThenBy(r => r.Path, StringComparer.Ordinal).ThenBy(r => r.Kind,
        StringComparer.Ordinal).ToImmutableArray();

    internal static LeanSourceContextInput Load(byte[] bytes, RepositorySnapshot current,
        RepositorySnapshot protectedBase)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        try
        {
            using var json = JsonDocument.Parse(bytes);
            return new(json.RootElement.Clone(), current, protectedBase);
        }
        catch (JsonException exception)
        { return new(null, current, protectedBase, exception.Message); }
    }

    internal LeanSourceFileContext GetRegistration(RepositorySnapshot snapshot, RepoPath path,
        string side, string reference)
    {
        if (reference == "current" || RelevantExternalInputsEqual(snapshot, path))
            return GetFile(snapshot, path, side);
        var row = Demand(path, side, "registrations", "registration");
        try
        {
            Bind(row, "sourceSha256", SourceHash(snapshot.Files[path]));
            Bind(row, "producerSha256", ProducerHash(current ?? snapshot));
            Bind(row, "configurationSha256", ConfigurationHash(current ?? snapshot));
            Bind(row, "referenceConfigurationSha256", ConfigurationHash(protectedBase ?? snapshot));
            Bind(row, "graphSha256", GraphHash(snapshot, path));
            BindInterfaces(row, snapshot, path);
            var result = row.GetProperty("result");
            var error = result.GetProperty("error");
            if (error.ValueKind != JsonValueKind.Null)
                throw Failure(path, "unknown registration effect: " + error.GetProperty("message").GetString(),
                    error.GetProperty("line").GetInt32());
            BindOrigins(row, snapshot, path, protectedBase ?? snapshot, current ?? snapshot);
            BindHeader(result, snapshot.Files[path]);
            var header = result.GetProperty("headerEnd").GetInt32();
            CheckOffset(snapshot.Files[path], header);
            var context = new LeanSourceFileContext(header, result.GetProperty("initialEquality").GetBoolean(),
                Commands(result.GetProperty("commands"), snapshot.Files[path], header, snapshot.Files[path].RawBytes.Length));
            ValidateCoverage(snapshot.Files[path], context);
            return context;
        }
        catch (Exception e) when (e is JsonException or InvalidOperationException or KeyNotFoundException
            or ArgumentException or FormatException && e is not LeanSourceExtractionException)
        { malformed.Add(e.Message); throw Failure(path, "malformed or stale registration context: " + e.Message); }
    }

    private bool RelevantExternalInputsEqual(RepositorySnapshot snapshot, RepoPath path)
    {
        if (current is null || protectedBase is null) return false;
        bool Same(string name) => current.TryGetFile(name, out var now)
            ? protectedBase.TryGetFile(name, out var old) && now.RawBytes.AsSpan().SequenceEqual(old.RawBytes.AsSpan())
            : !protectedBase.TryGetFile(name, out _);
        if (!Same("lean-toolchain")) return false;
        var seen = new HashSet<RepoPath>();
        var pending = new Queue<RepoPath>();
        pending.Enqueue(path);
        while (pending.TryDequeue(out var next))
        {
            if (!seen.Add(next) || !snapshot.Files.TryGetValue(next, out var file)) continue;
            foreach (var import in LeanSourceHeader.Read(file.Text).Imports)
            {
                if (snapshot.TryGetFile(import.Module.Replace('.', '/') + ".lean", out var managed)
                    && LeanClosureValidator.IsManagedLean(managed.Path.Value))
                    pending.Enqueue(managed.Path);
                else if (!(import.Module is "Init" or "Lean" or "Std"
                    || import.Module.StartsWith("Init.", StringComparison.Ordinal)
                    || import.Module.StartsWith("Lean.", StringComparison.Ordinal)
                    || import.Module.StartsWith("Std.", StringComparison.Ordinal)) && !Same("lake-manifest.json"))
                    return false;
            }
        }
        return true;
    }

    internal LeanSourceFileContext GetFile(RepositorySnapshot snapshot, RepoPath path, string side)
    {
        if (!snapshot.Files.TryGetValue(path, out var source))
            throw Failure(path, "demanded source is missing");
        var key = (snapshot, side, path);
        if (files.TryGetValue(key, out var cached)) return cached;
        var row = Demand(path, side, "files", "commands");
        try
        {
            Bind(row, "sourceSha256", SourceHash(source));
            Bind(row, "producerSha256", ProducerHash(current ?? snapshot));
            Bind(row, "configurationSha256", ConfigurationHash(current ?? snapshot));
            Bind(row, "graphSha256", GraphHash(snapshot, path));
            BindInterfaces(row, snapshot, path);
            var result = row.GetProperty("result");
            var error = result.GetProperty("error");
            if (error.ValueKind != JsonValueKind.Null)
                throw Failure(path, error.GetProperty("message").GetString()!, error.GetProperty("line").GetInt32());
            BindHeader(result, source);
            var header = result.GetProperty("headerEnd").GetInt32();
            CheckOffset(source, header);
            var initial = result.GetProperty("initialEquality").GetBoolean();
            var commands = Commands(result.GetProperty("commands"), source, header, source.RawBytes.Length);
            var context = new LeanSourceFileContext(header, initial, commands);
            ValidateCoverage(source, context);
            files.Add(key, context);
            return context;
        }
        catch (Exception e) when (e is JsonException or InvalidOperationException or KeyNotFoundException
            or ArgumentException or FormatException && e is not LeanSourceExtractionException)
        { malformed.Add(e.Message); throw Failure(path, "malformed or stale context: " + e.Message); }
    }

    private JsonElement Demand(RepoPath path, string side, string collection, string kind)
    {
        if (side is not ("current" or "protected")) throw Failure(path, "invalid source side");
        if (documentError is { } error)
        {
            malformed.Add(error);
            throw Failure(path, "malformed context bundle: " + error);
        }
        if (document is not { } root)
        {
            requests.Add(new(side, path.Value, kind));
            throw Failure(path, "missing demanded " + kind + " input");
        }
        try
        {
            if (root.GetProperty("schema").GetString() != Schema)
                throw new FormatException("source context schema mismatch");
            var matching = root.GetProperty(collection).EnumerateArray().Where(row =>
                row.GetProperty("side").GetString() == side
                && row.GetProperty("path").GetString() == path.Value).ToArray();
            if (matching.Length == 0)
            {
                requests.Add(new(side, path.Value, kind));
                throw Failure(path, "missing demanded " + kind + " input");
            }
            if (matching.Length != 1) throw new FormatException("duplicate demanded " + kind + " input");
            return matching[0];
        }
        catch (Exception e) when (e is JsonException or InvalidOperationException or KeyNotFoundException
            or FormatException && e is not LeanSourceExtractionException)
        { malformed.Add(e.Message); throw Failure(path, "malformed context bundle: " + e.Message); }
    }

    private static ImmutableArray<LeanSourceCommand> Commands(JsonElement rows, RepositoryFile file,
        int minimum, int maximum)
    {
        var commands = ImmutableArray.CreateBuilder<LeanSourceCommand>();
        var previous = minimum;
        foreach (var row in rows.EnumerateArray())
        {
            var start = row.GetProperty("start").GetInt32();
            var end = row.GetProperty("end").GetInt32();
            CheckOffset(file, start);
            CheckOffset(file, end);
            if (start < previous || end <= start || end > maximum)
                throw new FormatException("command spans overlap or lie outside their enclosing source");
            var kind = row.GetProperty("kind").GetString()!;
            var ns = row.GetProperty("namespace").GetString()!;
            if (string.IsNullOrWhiteSpace(kind) || ns is null)
                throw new FormatException("missing command kind or namespace");
            commands.Add(new(start, end, kind, ns, row.GetProperty("equality").GetBoolean(),
                Commands(row.GetProperty("children"), file, start, end)));
            previous = end;
        }
        return commands.ToImmutable();
    }

    private static void CheckOffset(RepositoryFile file, int offset)
    {
        if (offset < 0 || offset > file.RawBytes.Length
            || offset < file.RawBytes.Length && (file.RawBytes[offset] & 0xC0) == 0x80)
            throw new FormatException("source offset is not a UTF-8 boundary");
    }

    private static void ValidateCoverage(RepositoryFile file, LeanSourceFileContext context)
    {
        foreach (var token in LeanSourceTokenizer.Tokenize(file.Text, context.EqualityAt))
        {
            if (token.ByteOffset < context.HeaderEnd) continue;
            var end = token.ByteOffset + Encoding.UTF8.GetByteCount(token.Text);
            if (!context.Commands.Any(command => command.Start <= token.ByteOffset && end <= command.End))
                throw new FormatException("command spans omit source material at line " + token.Line);
        }
    }

    private static void Bind(JsonElement row, string property, string expected)
    {
        if (row.GetProperty(property).GetString() != expected)
            throw new FormatException(property + " does not match demanded input");
    }

    internal static ImmutableArray<RepositoryFile> InterfaceSources(RepositorySnapshot snapshot, RepoPath root)
    {
        var result = ImmutableArray.CreateBuilder<RepositoryFile>();
        var seen = new HashSet<RepoPath> { root };
        var pending = new Queue<RepoPath>();
        pending.Enqueue(root);
        while (pending.TryDequeue(out var path))
        {
            foreach (var import in LeanSourceHeader.Read(snapshot.Files[path].Text).Imports)
                if (snapshot.TryGetFile(import.Module.Replace('.', '/') + ".lean", out var source)
                    && LeanClosureValidator.IsManagedLean(source.Path.Value) && seen.Add(source.Path))
                { result.Add(source); pending.Enqueue(source.Path); }
        }
        return result.OrderBy(source => source.Path.Value, StringComparer.Ordinal).ToImmutableArray();
    }

    private static void BindInterfaces(JsonElement row, RepositorySnapshot snapshot, RepoPath root)
    {
        var actual = row.GetProperty("interfaces").EnumerateArray().Select(entry => (
            entry.GetProperty("path").GetString() ?? throw new FormatException("missing interface path"),
            entry.GetProperty("sourceSha256").GetString() ?? throw new FormatException("missing interface hash")))
            .OrderBy(entry => entry.Item1, StringComparer.Ordinal).ToArray();
        var expected = InterfaceSources(snapshot, root).Select(source => (source.Path.Value, SourceHash(source)));
        if (!actual.SequenceEqual(expected)) throw new FormatException("managed interface source bindings do not match");
    }

    private static void BindHeader(JsonElement result, RepositoryFile source)
    {
        var header = LeanSourceHeader.Read(source.Text);
        var imports = result.GetProperty("imports").EnumerateArray().Select(i => new LeanSourceImport(
            i.GetProperty("module").GetString() ?? throw new FormatException("missing import module"),
            i.GetProperty("importAll").GetBoolean(), i.GetProperty("isExported").GetBoolean(),
            i.GetProperty("isMeta").GetBoolean())).ToArray();
        if (header.IsModule != result.GetProperty("isModule").GetBoolean()
            || !header.Imports.SequenceEqual(imports) || header.End != result.GetProperty("headerEnd").GetInt32())
            throw new FormatException("compiler header descriptors disagree with source header");
    }

    private static void BindOrigins(JsonElement row, RepositorySnapshot snapshot, RepoPath root,
        RepositorySnapshot reference, RepositorySnapshot compiler)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var sources = new Dictionary<string, string>(StringComparer.Ordinal);
        using var manifest = JsonDocument.Parse(reference.TryGetFile("lake-manifest.json", out var file)
            ? file.Text : "{}");
        foreach (var origin in row.GetProperty("origins").EnumerateArray())
        {
            var module = origin.GetProperty("module").GetString()!;
            if (!seen.Add(module)) throw new FormatException("duplicate demanded source origin: " + module);
            sources.Add(module, origin.GetProperty("source").GetString()!);
            var data = Encoding.UTF8.GetBytes(origin.GetProperty("source").GetString()!);
            Bind(origin, "sha256", Hash(data));
            var blob = Encoding.UTF8.GetBytes("blob " + data.Length + "\0").Concat(data).ToArray();
            Bind(origin, "blob", Convert.ToHexStringLower(SHA1.HashData(blob)));
            var package = origin.GetProperty("package").GetString();
            if (package == "lean4")
            {
                Bind(origin, "pin", reference.Files[RepoPath.CreateKnown("lean-toolchain")].Text.Trim());
                Bind(origin, "path", "src/" + module.Replace('.', '/') + ".lean");
                Bind(origin, "url", "https://github.com/leanprover/lean4");
                var revision = origin.GetProperty("revision").GetString();
                if (revision is null || revision.Length != 40 || !revision.All(char.IsAsciiHexDigit))
                    throw new FormatException("Lean core source revision is not immutable");
            }
            else
            {
                var expected = manifest.RootElement.GetProperty("packages").EnumerateArray()
                    .Single(entry => entry.GetProperty("name").GetString() == package);
                Bind(origin, "revision", expected.GetProperty("rev").GetString()!);
                Bind(origin, "url", expected.GetProperty("url").GetString()!);
                Bind(origin, "path", module.Replace('.', '/') + ".lean");
            }
        }
        // Traverse exactly the snapshot's import graph. Same-current core imports
        // are compiler inputs; every other source-data module must be present.
        var pending = new Queue<string>();
        foreach (var source in InterfaceSources(snapshot, root).Prepend(snapshot.Files[root]))
            foreach (var import in LeanSourceHeader.Read(source.Text).Imports) pending.Enqueue(import.Module);
        var reached = new HashSet<string>(StringComparer.Ordinal);
        var managed = InterfaceSources(snapshot, root).Select(f => LeanImportClosure.ModuleName(f.Path))
            .Append(LeanImportClosure.ModuleName(root)).ToHashSet(StringComparer.Ordinal);
        var sameCore = reference.TryGetFile("lean-toolchain", out var oldCore)
            ? compiler.TryGetFile("lean-toolchain", out var newCore) && oldCore.RawBytes.AsSpan().SequenceEqual(newCore.RawBytes.AsSpan())
            : !compiler.TryGetFile("lean-toolchain", out _);
        while (pending.TryDequeue(out var module))
        {
            if (managed.Contains(module) || !reached.Add(module)) continue;
            if (sameCore && IsCore(module)) continue;
            if (!sources.TryGetValue(module, out var source))
                throw new FormatException("missing demanded external source origin: " + module);
            foreach (var import in LeanSourceHeader.Read(source).Imports) pending.Enqueue(import.Module);
        }
        if (sources.Keys.Any(module => !reached.Contains(module)))
            throw new FormatException("external source origin is outside the demanded import graph");
    }

    private static bool IsCore(string module) => module.Split('.')[0] is "Init" or "Lean" or "Std";

    internal static string SourceHash(RepositoryFile file) => Hash(file.RawBytes.AsSpan());
    internal static string ProducerHash(RepositorySnapshot snapshot) => HashFields(
        new[] { "tools/lean-inspector/SourceContext.lean", "tools/lean-inspector/SourceOptions.lean",
            "tools/lean-inspector/source-context.py", "tools/lean-inspector/source-context.sh",
            "tools/StrataLint.Cli/Commands/LeanSourceInputCommand.cs",
            "tools/StrataLint.Engine/Ledger/Admission/LeanSourceHeader.cs" }
            .Select(path => (path, snapshot.TryGetFile(path, out var file) ? SourceHash(file) : "missing")));

    internal static string ConfigurationHash(RepositorySnapshot snapshot) => HashFields(
        new[] { "lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml" }
            .Select(path => (path, snapshot.TryGetFile(path, out var file) ? SourceHash(file) : "missing")));

    internal static string GraphHash(RepositorySnapshot snapshot, RepoPath path)
    {
        var visited = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Queue<RepoPath>();
        var fields = new List<(string, string)>();
        pending.Enqueue(path);
        while (pending.TryDequeue(out var next))
        {
            if (!visited.Add(next.Value) || !snapshot.Files.TryGetValue(next, out var file)) continue;
            var header = LeanSourceHeader.Read(file.Text);
            fields.Add((next.Value, JsonSerializer.Serialize(new { header.IsModule, header.Prelude, header.Imports })));
            foreach (var import in header.Imports)
            {
                if (RepoPath.TryCreate(import.Module.Replace('.', '/') + ".lean", out var imported)
                    && LeanClosureValidator.IsManagedLean(imported.Value) && snapshot.Files.ContainsKey(imported)) pending.Enqueue(imported);
            }
        }
        return HashFields(fields.OrderBy(f => f.Item1, StringComparer.Ordinal));
    }

    private static string HashFields(IEnumerable<(string Name, string Value)> fields) =>
        Hash(Encoding.UTF8.GetBytes(string.Concat(fields.Select(f => f.Name + "\0" + f.Value + "\n"))));
    private static string Hash(ReadOnlySpan<byte> bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));
    private static LeanSourceExtractionException Failure(RepoPath path, string message, int line = 1) =>
        new($"SOURCE_CONTEXT {path.Value}:{line}: {message}", line);
}

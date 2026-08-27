using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal static class RawLeanReportArtifact
{
    internal const string Schema = "stratalint-raw-lean-report-v2";
    internal const string DefaultRelativePath = ".lake/build/stratalint/raw-lean-report.json";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    internal static LeanAxiomReport ReadFile(string path, RepositorySnapshot snapshot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(path);
        var fullPath = Path.GetFullPath(path);
        var bytes = File.ReadAllBytes(fullPath);
        return Read(bytes, snapshot, MaterialsPath(fullPath));
    }

    internal static LeanAxiomReport Read(ReadOnlySpan<byte> bytes, RepositorySnapshot snapshot)
        => Read(bytes, snapshot, materialPath: null);

    private static LeanAxiomReport Read(
        ReadOnlySpan<byte> bytes,
        RepositorySnapshot snapshot,
        string? materialPath)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var text = StrictUtf8.GetString(bytes);
        ImmutableArray<byte> canonical;
        try
        {
            canonical = StructuredCanonicalWriter.WriteJson(text);
        }
        catch (JsonException exception)
        {
            throw new FormatException("Raw Lean report is not valid JSON.", exception);
        }

        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            var mismatch = FirstMismatch(canonical.AsSpan(), bytes);
            throw new FormatException(
                "Raw Lean report bytes are not canonical JSON at byte "
                + $"{mismatch}: expected {ByteAt(canonical.AsSpan(), mismatch)}, "
                + $"actual {ByteAt(bytes, mismatch)}.");
        }

        using var document = JsonDocument.Parse(text);
        var root = document.RootElement;
        RequireProperties(root, ["modules", "schema"], "raw Lean report");
        if (RequiredString(root, "schema") != Schema)
        {
            throw new FormatException($"Raw Lean report schema must be {Schema}.");
        }

        var expected = ExpectedModules(snapshot);
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
        var materialArchive = materialPath is null
            ? null
            : StatementMaterialArchive.Open(
                materialPath,
                () => reports.Values
                    .SelectMany(static report => report.Declarations)
                    .Select(static declaration => declaration.StatementTypeAddress));
        string? previousModule = null;
        foreach (var moduleElement in RequiredArray(root, "modules").EnumerateArray())
        {
            RequireProperties(
                moduleElement,
                ["declarations", "imports", "module", "source_path", "source_sha256"],
                "raw Lean module");
            var module = RequiredString(moduleElement, "module");
            RequireStrictOrder(previousModule, module, "modules");
            previousModule = module;
            var sourcePath = RequiredString(moduleElement, "source_path");
            if (!expected.TryGetValue(module, out var source))
            {
                throw new FormatException($"Raw Lean report contains unknown module {module}.");
            }

            if (!string.Equals(source.Path.Value, sourcePath, StringComparison.Ordinal))
            {
                throw new FormatException($"Raw Lean report maps {module} to unexpected path {sourcePath}.");
            }

            var sourceSha256 = RequiredString(moduleElement, "source_sha256");
            var expectedSourceSha256 = Sha256(source.File.RawBytes.AsSpan());
            if (!string.Equals(sourceSha256, expectedSourceSha256, StringComparison.Ordinal))
            {
                throw new FormatException($"Raw Lean report source hash does not match {sourcePath}.");
            }

            var imports = ReadSortedStrings(RequiredArray(moduleElement, "imports"), "imports");
            var declarations = ReadDeclarations(
                RequiredArray(moduleElement, "declarations"),
                materialArchive);
            if (!reports.TryAdd(sourcePath, new LeanFileReport(imports, declarations)))
            {
                throw new FormatException($"Raw Lean report contains duplicate path {sourcePath}.");
            }
        }

        var missing = expected.Values
            .Select(static item => item.Path.Value)
            .Where(path => !reports.ContainsKey(path))
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (missing.Length > 0)
        {
            throw new FormatException(
                "Raw Lean report is missing modules: " + string.Join(", ", missing));
        }

        return LeanAxiomReport.Create(reports);
    }

    internal static ImmutableArray<byte> Write(RepositorySnapshot snapshot, LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(report);
        var expected = ExpectedModules(snapshot);
        var material = JsonSerializer.SerializeToElement(new
        {
            modules = expected
                .OrderBy(static item => item.Key, StringComparer.Ordinal)
                .Select(item =>
                {
                    if (!report.Files.TryGetValue(item.Value.Path, out var fileReport))
                    {
                        throw new FormatException(
                            $"Lean report is missing {item.Value.Path.Value}.");
                    }

                    return new
                    {
                        declarations = fileReport.Declarations
                            .OrderBy(static declaration => declaration.NameKey, StringComparer.Ordinal)
                            .ThenBy(static declaration => declaration.Kind, StringComparer.Ordinal)
                            .ThenBy(static declaration => declaration.Name, StringComparer.Ordinal)
                            .Select(declaration => new
                            {
                                axioms = declaration.Axioms
                                    .Distinct(StringComparer.Ordinal)
                                    .Order(StringComparer.Ordinal),
                                include_in_statement = declaration.IncludeInStatement,
                                kind = declaration.Kind,
                                name = declaration.Name,
                                name_key = declaration.NameKey,
                                statement_id = DeclarationStatementId(item.Value.Path, declaration),
                                type_sha256 = declaration.StatementTypeAddress,
                            }),
                        imports = fileReport.Imports
                            .Distinct(StringComparer.Ordinal)
                            .Order(StringComparer.Ordinal),
                        module = item.Key,
                        source_path = item.Value.Path.Value,
                        source_sha256 = Sha256(item.Value.File.RawBytes.AsSpan()),
                    };
                }),
            schema = Schema,
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    internal static void WriteFile(
        string path,
        RepositorySnapshot snapshot,
        LeanAxiomReport report)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(path);
        var fullPath = Path.GetFullPath(path);
        var materials = MaterialsPath(fullPath);
        if (Directory.Exists(materials))
        {
            Directory.Delete(materials, recursive: true);
        }
        if (File.Exists(materials))
        {
            File.Delete(materials);
        }

        var materialByAddress = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var declaration in report.Files.Values
                     .SelectMany(static file => file.Declarations))
        {
            var value = declaration.LoadTypeRepresentation();
            var address = StatementTypeAddress(value);
            if (!string.Equals(address, declaration.StatementTypeAddress, StringComparison.Ordinal))
            {
                throw new InvalidDataException(
                    $"Lean declaration {declaration.Name} statement material hash does not match its address.");
            }

            if (materialByAddress.TryGetValue(address, out var previous))
            {
                if (!string.Equals(previous, value, StringComparison.Ordinal))
                {
                    throw new InvalidDataException(
                        $"Lean statement material address collision for {address}.");
                }
            }
            else
            {
                materialByAddress.Add(address, value);
            }
        }

        Directory.CreateDirectory(
            Path.GetDirectoryName(fullPath)
                ?? throw new InvalidOperationException("Raw Lean report path has no parent."));
        using (var stream = File.Create(materials))
        using (var archive = new ZipArchive(stream, ZipArchiveMode.Create, leaveOpen: false))
        {
            foreach (var (address, value) in materialByAddress)
            {
                var entry = archive.CreateEntry(
                    StatementMaterialArchive.EntryName(address),
                    CompressionLevel.SmallestSize);
                entry.LastWriteTime = StatementMaterialArchive.CanonicalTimestamp;
                using var destination = entry.Open();
                destination.Write(StrictUtf8.GetBytes(value));
            }
        }
        File.WriteAllBytes(fullPath, Write(snapshot, report).AsSpan());
    }

    internal static string MaterialsPath(string reportPath) =>
        Path.GetFullPath(reportPath) + ".materials.zip";

    internal static string ContentAddress(ReadOnlySpan<byte> canonicalBytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(canonicalBytes));

    internal static string DefaultPath(string repositoryRoot) => Path.Combine(
        Path.GetFullPath(repositoryRoot),
        DefaultRelativePath.Replace('/', Path.DirectorySeparatorChar));

    internal static Func<string, string> OpenStatementMaterialSource(
        string reportPath,
        IEnumerable<string> addresses)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(reportPath);
        ArgumentNullException.ThrowIfNull(addresses);
        var archive = StatementMaterialArchive.Open(MaterialsPath(reportPath), addresses);
        return archive.Read;
    }

    private static ImmutableArray<LeanDeclaration> ReadDeclarations(
        JsonElement declarations,
        StatementMaterialArchive? materialArchive)
    {
        var builder = ImmutableArray.CreateBuilder<LeanDeclaration>();
        string? previousNameKey = null;
        foreach (var declarationElement in declarations.EnumerateArray())
        {
            RequireProperties(
                declarationElement,
                [
                    "axioms", "include_in_statement", "kind", "name", "name_key",
                    "statement_id", "type_sha256",
                ],
                "raw Lean declaration");
            var nameKey = RequiredString(declarationElement, "name_key");
            RequireStrictOrder(previousNameKey, nameKey, "declarations");
            previousNameKey = nameKey;
            var statementTypeAddress = RequiredString(declarationElement, "type_sha256");
            var statementId = RequiredString(declarationElement, "statement_id");
            if (!FrozenHashSyntax.IsSha256(statementTypeAddress)
                || !FrozenHashSyntax.IsSha256(statementId))
            {
                throw new FormatException(
                    "Raw Lean declaration statement addresses must be canonical SHA-256 values.");
            }

            builder.Add(new LeanDeclaration(
                RequiredString(declarationElement, "name"),
                RequiredString(declarationElement, "kind"),
                statementTypeAddress,
                statementId,
                ReadSortedStrings(RequiredArray(declarationElement, "axioms"), "axioms"),
                materialArchive is null
                    ? () => throw new InvalidDataException(
                        "Lean declaration has no statement material source; read the report from its file path.")
                    : () => materialArchive.Read(statementTypeAddress))
            {
                IncludeInStatement = RequiredBoolean(declarationElement, "include_in_statement"),
                NameKey = nameKey,
            });
        }

        return builder.ToImmutable();
    }

    private sealed class StatementMaterialArchive
    {
        private const string EntryPrefix = "sha256/";
        private readonly Lazy<ArchiveContents> contents;
        private readonly Lazy<bool> addressesValidated;
        private readonly ConcurrentDictionary<string, Lazy<string>> material = new(StringComparer.Ordinal);

        private StatementMaterialArchive(string path, Func<IEnumerable<string>> expectedAddresses)
        {
            ArgumentException.ThrowIfNullOrWhiteSpace(path);
            ArgumentNullException.ThrowIfNull(expectedAddresses);
            var fullPath = Path.GetFullPath(path);
            contents = new Lazy<ArchiveContents>(
                () => Load(fullPath),
                LazyThreadSafetyMode.ExecutionAndPublication);
            addressesValidated = new Lazy<bool>(
                () =>
                {
                    ValidateAddresses(expectedAddresses(), contents.Value);
                    return true;
                },
                LazyThreadSafetyMode.ExecutionAndPublication);
        }

        internal static DateTimeOffset CanonicalTimestamp { get; } =
            new(1980, 1, 1, 0, 0, 0, TimeSpan.Zero);

        internal static StatementMaterialArchive Open(
            string path,
            IEnumerable<string> expectedAddresses) =>
            new(path, () => expectedAddresses);

        internal static StatementMaterialArchive Open(
            string path,
            Func<IEnumerable<string>> expectedAddresses) =>
            new(path, expectedAddresses);

        private static ArchiveContents Load(string path)
        {
            if (!File.Exists(path))
            {
                throw new InvalidDataException($"Lean statement material archive is missing: {path}");
            }

            try
            {
                var archive = new ZipArchive(
                    new MemoryStream(File.ReadAllBytes(path), writable: false),
                    ZipArchiveMode.Read);
                var builder = ImmutableDictionary.CreateBuilder<string, ZipArchiveEntry>(StringComparer.Ordinal);
                foreach (var entry in archive.Entries)
                {
                    if (!entry.FullName.StartsWith(EntryPrefix, StringComparison.Ordinal)
                        || !FrozenHashSyntax.IsSha256("sha256:" + entry.FullName[EntryPrefix.Length..])
                        || !builder.TryAdd(entry.FullName, entry))
                    {
                        throw new InvalidDataException(
                            $"Lean statement material archive has a malformed or duplicate entry: {path}");
                    }
                }

                return new ArchiveContents(archive, builder.ToImmutable());
            }
            catch (InvalidDataException exception)
            {
                throw new InvalidDataException(
                    $"Lean statement material archive is invalid: {path}", exception);
            }
            catch (IOException exception)
            {
                throw new InvalidDataException(
                    $"Lean statement material archive cannot be read: {path}", exception);
            }
        }

        internal static string EntryName(string address) => EntryPrefix + address[7..];

        private static void ValidateAddresses(
            IEnumerable<string> addresses,
            ArchiveContents archive)
        {
            var expected = addresses
                .Select(EntryName)
                .ToImmutableHashSet(StringComparer.Ordinal);
            var missing = expected
                .Except(archive.Entries.Keys, StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .FirstOrDefault();
            if (missing is not null)
            {
                throw new InvalidDataException(
                    $"Lean statement material archive is missing {missing}.");
            }

            var extra = archive.Entries.Keys
                .Except(expected, StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .FirstOrDefault();
            if (extra is not null)
            {
                throw new InvalidDataException(
                    $"Lean statement material archive has unreferenced entry {extra}.");
            }
        }

        internal string Read(string address)
        {
            if (!FrozenHashSyntax.IsSha256(address))
            {
                throw new InvalidDataException("Lean statement material address is malformed.");
            }

            _ = addressesValidated.Value;
            return material.GetOrAdd(
                address,
                value => new Lazy<string>(
                    () => ReadCore(value),
                    LazyThreadSafetyMode.ExecutionAndPublication)).Value;
        }

        private string ReadCore(string address)
        {
            var archive = contents.Value;
            if (!archive.Entries.TryGetValue(EntryName(address), out var entry))
            {
                throw new InvalidDataException($"Lean statement material is missing for {address}.");
            }
            if (entry.Length > int.MaxValue)
            {
                throw new InvalidDataException($"Lean statement material is too large for {address}.");
            }

            var bytes = new byte[(int)entry.Length];
            lock (archive.Gate)
            {
                using var stream = entry.Open();
                stream.ReadExactly(bytes);
            }

            string value;
            try
            {
                value = StrictUtf8.GetString(bytes);
            }
            catch (DecoderFallbackException exception)
            {
                throw new InvalidDataException(
                    $"Lean statement material is not strict UTF-8 for {address}.",
                    exception);
            }

            var actual = FrozenContentHash.Compute(FrozenHashDomains.Statement, bytes);
            if (!string.Equals(actual, address, StringComparison.Ordinal))
            {
                throw new InvalidDataException(
                    $"Lean statement material hash mismatch for {address}: actual {actual}.");
            }

            return value;
        }

        private sealed class ArchiveContents(ZipArchive archive, ImmutableDictionary<string, ZipArchiveEntry> entries)
        {
            internal object Gate { get; } = new();

            internal ZipArchive Archive { get; } = archive;

            internal ImmutableDictionary<string, ZipArchiveEntry> Entries { get; } = entries;
        }
    }

    private static string DeclarationStatementId(RepoPath path, LeanDeclaration declaration) =>
        CanonicalStatementWriter.DeclarationStatementId(path, declaration);

    private static string StatementTypeAddress(string value) =>
        FrozenContentHash.Compute(FrozenHashDomains.Statement, StrictUtf8.GetBytes(value));

    private static ImmutableArray<string> ReadSortedStrings(JsonElement array, string context)
    {
        var builder = ImmutableArray.CreateBuilder<string>();
        string? previous = null;
        foreach (var element in array.EnumerateArray())
        {
            if (element.ValueKind != JsonValueKind.String || element.GetString() is not { } value)
            {
                throw new FormatException($"Raw Lean report {context} must contain strings.");
            }

            RequireStrictOrder(previous, value, context);
            previous = value;
            builder.Add(value);
        }

        return builder.ToImmutable();
    }

    private static void RequireStrictOrder(string? previous, string current, string context)
    {
        if (previous is not null && string.CompareOrdinal(previous, current) >= 0)
        {
            throw new FormatException($"Raw Lean report {context} must be sorted and unique.");
        }
    }

    private static int FirstMismatch(ReadOnlySpan<byte> expected, ReadOnlySpan<byte> actual)
    {
        var shared = Math.Min(expected.Length, actual.Length);
        for (var index = 0; index < shared; index++)
        {
            if (expected[index] != actual[index]) return index;
        }

        return shared;
    }

    private static string ByteAt(ReadOnlySpan<byte> bytes, int index) =>
        index < bytes.Length ? $"0x{bytes[index]:x2}" : "end-of-file";

    private static Dictionary<string, (RepoPath Path, RepositoryFile File)> ExpectedModules(
        RepositorySnapshot snapshot) => snapshot.Files
        .Where(static item => LeanClosureValidator.IsManagedLean(item.Key.Value))
        .ToDictionary(
            static item => ModuleName(item.Key.Value),
            static item => (item.Key, item.Value),
            StringComparer.Ordinal);

    private static string ModuleName(string path) => path == "Trureturing.lean"
        ? "Trureturing"
        : path[..^5].Replace('/', '.');

    private static string Sha256(ReadOnlySpan<byte> bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static JsonElement RequiredArray(JsonElement element, string property) =>
        element.TryGetProperty(property, out var child) && child.ValueKind == JsonValueKind.Array
            ? child
            : throw new FormatException($"Raw Lean report field {property} must be an array.");

    private static string RequiredString(JsonElement element, string property) =>
        element.TryGetProperty(property, out var child) && child.ValueKind == JsonValueKind.String
            ? child.GetString() ?? throw new FormatException($"Raw Lean report field {property} is null.")
            : throw new FormatException($"Raw Lean report field {property} must be a string.");

    private static bool RequiredBoolean(JsonElement element, string property) =>
        element.TryGetProperty(property, out var child)
            && child.ValueKind is JsonValueKind.True or JsonValueKind.False
                ? child.GetBoolean()
                : throw new FormatException($"Raw Lean report field {property} must be a boolean.");

    private static void RequireProperties(
        JsonElement element,
        IReadOnlyCollection<string> expected,
        string context)
    {
        if (element.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"{context} must be an object.");
        }

        var actual = element.EnumerateObject().Select(static property => property.Name).ToArray();
        if (actual.Length != expected.Count
            || !actual.Order(StringComparer.Ordinal).SequenceEqual(expected.Order(StringComparer.Ordinal)))
        {
            throw new FormatException($"{context} has unexpected fields.");
        }
    }
}

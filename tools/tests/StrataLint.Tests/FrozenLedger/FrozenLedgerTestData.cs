using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class FrozenLedgerTestData
{
    internal static FrozenMaterialCatalog BuildCatalog(params ModuleSpec[] modules) =>
        BuildCatalogWithEnvironment(
            "leanprover/lean4:v4.24.0\n",
            "[package]\nname = \"fixture\"\n",
            "{}\n",
            GitOid('a'),
            GitOid('b'),
            modules);

    internal static FrozenMaterialCatalog BuildCatalogWithEnvironment(
        string toolchain,
        string lakefile,
        string manifest,
        string originCommitOid,
        string originTreeOid,
        params ModuleSpec[] modules)
    {
        _ = originCommitOid;
        _ = originTreeOid;
        var (snapshot, closure, states, adjacency) = BuildTruthGraph(
            toolchain,
            lakefile,
            manifest,
            modules);
        return Assert.IsType<FrozenMaterialOutcome.Accepted>(
            FrozenContentAddress.Build(snapshot, closure, states, adjacency)).Capability;
    }

    internal static FrozenMaterialCatalog BuildAdmissionCatalog(
        IEnumerable<string> selectedModules,
        IReadOnlyDictionary<RepoPath, FrozenActiveEntry> trustedBaseEntries,
        params ModuleSpec[] modules)
    {
        var (snapshot, closure, states, adjacency) = BuildTruthGraph(
            "leanprover/lean4:v4.24.0\n",
            "[package]\nname = \"fixture\"\n",
            "{}\n",
            modules);
        return FrozenContentAddress.BuildAdmissionCatalog(
            snapshot,
            closure,
            states,
            adjacency,
            selectedModules.Select(RepoPathFor).ToHashSet(),
            trustedBaseEntries);
    }

    private static (
        RepositorySnapshot Snapshot,
        AcceptedLeanClosure Closure,
        ImmutableDictionary<RepoPath, TruthState> States,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> Adjacency) BuildTruthGraph(
        string toolchain,
        string lakefile,
        string manifest,
        params ModuleSpec[] modules)
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["lean-toolchain"] = toolchain,
            ["lakefile.toml"] = lakefile,
            ["lake-manifest.json"] = manifest,
        };
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
        foreach (var module in modules)
        {
            files[PathFor(module.Name)] = module.Source;
            var declarationNames = module.Declarations.IsDefaultOrEmpty
                ? ImmutableArray.Create(module.Name.ToLowerInvariant())
                : module.Declarations;
            reports[PathFor(module.Name)] = new LeanFileReport(
                module.Imports.Select(ModuleNameFor).ToImmutableArray(),
                declarationNames
                    .Order(StringComparer.Ordinal)
                    .Select(name => new LeanDeclaration(
                        name,
                        module.Kind,
                        module.StatementMaterial,
                        module.Axioms)
                    {
                        NameKey = module.OpaqueNameKeys ? NameKeyFor(name) : $"ns(n0,{name.Length}:{name})",
                        IncludeInStatement = module.Excluded.IsDefaultOrEmpty
                            || !module.Excluded.Contains(name),
                    })
                    .ToImmutableArray());
        }

        var raw = RawRepositorySnapshot.Create(
            files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
        var states = LeanTruthStates.Resolve(snapshot, closure);
        var adjacency = LeanImportAdjacency.Build(snapshot, closure);
        return (snapshot, closure, states, adjacency);
    }

    internal static FrozenMaterialOutcome BuildCatalogOutcome(
        string path,
        string source,
        LeanFileReport report)
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [path] = source,
            ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
            ["lake-manifest.json"] = "{}\n",
        };
        var raw = RawRepositorySnapshot.Create(
            files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(
                snapshot,
                LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
                {
                    [path] = report,
                }))).Capability;
        var states = LeanTruthStates.Resolve(snapshot, closure);
        var adjacency = LeanImportAdjacency.Build(snapshot, closure);
        return FrozenContentAddress.Build(snapshot, closure, states, adjacency);
    }

    internal static ModuleSpec Module(
        string name,
        string? source = null,
        IReadOnlyList<string>? imports = null,
        IEnumerable<string>? axioms = null,
        string? baseCommitOid = null,
        string? baseTreeOid = null,
        IEnumerable<string>? declarations = null,
        IEnumerable<string>? excluded = null,
        bool opaqueNameKeys = false) =>
        new(
            name,
            source ?? $"theorem {name.ToLowerInvariant()} : True := by trivial\n",
            imports ?? Array.Empty<string>(),
            (axioms ?? Array.Empty<string>()).Order(StringComparer.Ordinal).ToImmutableArray(),
            baseCommitOid,
            baseTreeOid,
            declarations is null
                ? ImmutableArray<string>.Empty
                : declarations.Order(StringComparer.Ordinal).ToImmutableArray(),
            excluded is null
                ? ImmutableArray<string>.Empty
                : excluded.Order(StringComparer.Ordinal).ToImmutableArray(),
            opaqueNameKeys,
            "theorem",
            "True");

    internal static ModuleSpec ModuleWithReport(
        string name,
        string source,
        string statementMaterial,
        IEnumerable<string>? axioms = null,
        IEnumerable<string>? declarations = null,
        string kind = "theorem") =>
        Module(name, source, axioms: axioms, declarations: declarations) with
        {
            Kind = kind,
            StatementMaterial = statementMaterial,
        };

    /// Deliberately not derivable from the declaration name. A key an implementation could
    /// assemble from the selector would let it skip the report resolver entirely and still match.
    internal static string NameKeyFor(string name) =>
        "nk-" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(name)))[..16];

    internal static string PathFor(string module) => $"D5/S0/Carrier/{module}.lean";

    internal static RepoPath RepoPathFor(string module) =>
        RepoPath.TryCreate(PathFor(module), out var path)
            ? path
            : throw new InvalidOperationException("test path is invalid");

    internal static string GitOid(char digit) => $"git-sha1:{new string(digit, 40)}";

    internal static string GitBlobOid(string text)
    {
        var bytes = Encoding.UTF8.GetBytes(text);
        var header = Encoding.ASCII.GetBytes($"blob {bytes.Length}\0");
        return "git-sha1:" + Convert.ToHexStringLower(SHA1.HashData(header.Concat(bytes).ToArray()));
    }

    internal static string Sha256(string text) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(text)));

    internal static FrozenLedgerValidationOutcome ValidateHistory(
        ImmutableArray<RepositoryFile> files,
        FrozenMaterialCatalog catalog)
    {
        var snapshot = RepositorySnapshot.Create(files.ToImmutableDictionary(static file => file.Path));
        return FrozenLedger.ValidateTrustedHistory(FrozenLedgerBaseViewReader.Read(snapshot), catalog);
    }

    internal static FrozenLedgerConsistent Baseline(FrozenMaterialCatalog catalog) =>
        Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(EventFiles(catalog), catalog)).Capability;

    internal static FrozenLedgerBaseView BaseView(FrozenMaterialCatalog catalog)
    {
        var files = EventFiles(catalog);
        return FrozenLedgerBaseViewReader.Read(
            RepositorySnapshot.Create(files.ToImmutableDictionary(static file => file.Path)));
    }

    internal static FrozenLedgerValidationOutcome ValidateCandidate(
        ImmutableArray<DagLedgerFileEvent> events,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog) =>
        FrozenLedger.ValidateCandidate(events, baseline, catalog);

    internal static ImmutableArray<RepositoryFile> EventFiles(
        FrozenMaterialCatalog catalog,
        string? generatorBlobOid = null)
    {
        _ = generatorBlobOid;
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        foreach (var material in catalog.ClosedNodes.OrderBy(
            static item => item.RepoPath.Value,
            StringComparer.Ordinal))
        {
            var payload = FrozenLedgerCanonicalWriter.FreezePayload(material);
            files.Add(EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(payload)));
        }

        return files.ToImmutable();
    }

    internal static RepositoryFile EventFile(
        string eventType,
        JsonElement payload,
        int? schemaVersion = null)
    {
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(eventType, payload, schemaVersion);
        var identity = FrozenLedgerCanonicalWriter.EventIdentity(encoded.Hash);
        var path = RepoPath.CreateKnown(
            $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{identity[7..]}.json");
        return new RepositoryFile(
            path,
            encoded.Bytes,
            Encoding.UTF8.GetString(encoded.Bytes.AsSpan()));
    }

    internal static ImmutableArray<DagLedgerFileEvent> LoadEvents(
        IEnumerable<RepositoryFile> files,
        bool trusted = false)
    {
        var loaded = (trusted
            ? FrozenAcceptedEventLoader.LoadTrustedFiles(files)
            : FrozenAcceptedEventLoader.LoadFiles(files)) switch
        {
            DagLedgerFilesLoadOutcome.Loaded accepted => accepted.Events,
            DagLedgerFilesLoadOutcome.Invalid invalid => throw new Xunit.Sdk.XunitException(invalid.Message),
            _ => throw new InvalidOperationException("unknown frozen event load outcome"),
        };
        Assert.True(DagLedgerLoader.TryOrderClosedDag(
            loaded,
            ImmutableArray<string>.Empty,
            out var ordered));
        return ordered;
    }

    internal static ImmutableArray<DagLedgerFileEvent> LoadDrafts(
        FrozenLedgerBaseView baseView,
        IEnumerable<FrozenLedgerDraft> drafts) =>
        DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
            baseView,
            DagLedgerAppendWriter.BuildNewEventFiles(drafts),
            "test generated frozen event set");

    internal static void AddLedgerFiles(
        IDictionary<string, string> files,
        IEnumerable<RepositoryFile> events)
    {
        foreach (var item in events)
        {
            files[item.Path.Value] = item.Text;
        }
    }

    internal static void WriteLedgerDirectory(
        string directory,
        IEnumerable<RepositoryFile> events)
    {
        Directory.CreateDirectory(directory);
        DagLedgerAppendWriter.WriteEventFiles(directory, events);
    }

    internal static byte[] ReadLedgerDirectory(string directory) =>
        DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(directory)
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .SelectMany(static file => file.RawBytes)
            .ToArray();

    private static string ModuleNameFor(string module) => $"D5.S0.Carrier.{module}";

    internal sealed record ModuleSpec(
        string Name,
        string Source,
        IReadOnlyList<string> Imports,
        ImmutableArray<string> Axioms,
        string? BaseCommitOid,
        string? BaseTreeOid,
        ImmutableArray<string> Declarations = default,
        ImmutableArray<string> Excluded = default,
        bool OpaqueNameKeys = false,
        string Kind = "theorem",
        string StatementMaterial = "True");
}

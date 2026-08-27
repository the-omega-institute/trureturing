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
        var environment = new FrozenEnvironmentAttestation(
            originCommitOid,
            originTreeOid,
            GitBlobOid(files["lean-toolchain"]),
            GitBlobOid(files["lake-manifest.json"]))
        {
            LakefilePath = "lakefile.toml",
            LakefileBlobOid = GitBlobOid(files["lakefile.toml"]),
        };
        var attestations = modules.Select(module => new FrozenModuleAttestation(
            RepoPathFor(module.Name),
            GitBlobOid(module.Source))
        {
            BaseCommitOid = module.BaseCommitOid,
            BaseTreeOid = module.BaseTreeOid,
        });

        return Assert.IsType<FrozenMaterialOutcome.Accepted>(
            FrozenContentAddress.Build(snapshot, closure, states, adjacency, environment, attestations)).Capability;
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
        var environment = new FrozenEnvironmentAttestation(
            GitOid('a'),
            GitOid('b'),
            GitBlobOid(files["lean-toolchain"]),
            GitBlobOid(files["lake-manifest.json"]));
        return FrozenContentAddress.Build(
            snapshot, closure, states, adjacency, environment, Array.Empty<FrozenModuleAttestation>());
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

    internal static byte[][] Lines(ImmutableArray<byte> bytes)
    {
        var result = new List<byte[]>();
        var start = 0;
        for (var index = 0; index < bytes.Length; index++)
        {
            if (bytes[index] != (byte)'\n') continue;
            result.Add(bytes.AsSpan(start, index - start + 1).ToArray());
            start = index + 1;
        }

        Assert.Equal(bytes.Length, start);
        return result.ToArray();
    }

    internal static FrozenLedgerValidationOutcome ValidateGenesis(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog) =>
        FrozenLedger.ValidateGenesis(syntax, catalog, Trust(syntax));

    internal static FrozenLedgerValidationOutcome ValidateGenesis(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences references) =>
        FrozenLedger.ValidateGenesis(syntax, catalog, references);

    internal static FrozenLedgerValidationOutcome ValidateHistory(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog) =>
        FrozenLedger.ValidateHistory(syntax, catalog, Trust(syntax));

    internal static FrozenLedgerValidationOutcome ValidateCandidate(
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog) =>
        FrozenLedger.ValidateCandidate(syntax, baseline, catalog, Trust(syntax));

    internal static FrozenLedgerValidationOutcome ValidateCandidate(
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedRevocationReceiptStore receipts) =>
        FrozenLedger.ValidateCandidate(syntax, baseline, catalog, Trust(syntax), receipts);

    internal static FrozenLedgerValidationOutcome ValidateCandidate(
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences references,
        TrustedRevocationReceiptStore receipts) =>
        FrozenLedger.ValidateCandidate(syntax, baseline, catalog, references, receipts);

    internal static TrustedFrozenGitReferences Trust(FrozenLedgerSyntax syntax) =>
        TrustedFrozenGitReferences.CreateForTrustedAdapter(
            FrozenLedger.ScanReferences(syntax) is FrozenLedgerReferenceScanOutcome.Accepted accepted
                ? accepted.References.Inputs
                : ImmutableArray<FrozenLedgerInput>.Empty);

    internal static void AddLedgerFiles(
        IDictionary<string, string> files,
        ImmutableArray<byte> bytes)
    {
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes.AsSpan())).Syntax;
        foreach (var line in syntax.Lines)
        {
            var payload = line.Value.GetProperty("payload");
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                line.Value.GetProperty("event_type").GetString()!,
                payload);
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(encoded.Hash);
            files[$"{FrozenLedgerChangeClassifier.AcceptedRoot}/{identity[7..]}.json"] =
                Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        }
    }

    internal static void WriteLedgerDirectory(string directory, ImmutableArray<byte> bytes)
    {
        Directory.CreateDirectory(directory);
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes.AsSpan())).Syntax;
        DagLedgerAppendWriter.WriteNewEvents(directory, syntax.Lines);
    }

    internal static byte[] ReadLedgerDirectory(string directory) =>
        DagLedgerCommandPreparation.LoadLedgerDirectory(directory, "test frozen ledger").RawBytes.ToArray();

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

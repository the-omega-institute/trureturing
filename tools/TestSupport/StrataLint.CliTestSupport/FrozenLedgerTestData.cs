using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

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
                        NameKey = module.OpaqueNameKeys
                            ? NameKeyFor(name)
                            : CanonicalNameKeyFor(name),
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
        $"ns(n0,17:k{Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(name)))[..16]})";

    private static string CanonicalNameKeyFor(string name)
    {
        var key = "n0";
        foreach (var component in name.Split('.')) key = $"ns({key},{Encoding.UTF8.GetByteCount(component)}:{component})";
        return key;
    }

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

    internal static ImmutableArray<RepositoryFile> StateFiles(FrozenMaterialCatalog catalog) =>
        catalog.ClosedNodes.OrderBy(static item => item.RepoPath.Value, StringComparer.Ordinal)
            .Select(static material =>
            {
                var bytes = FrozenStateRecord.Encode(material.StatementId,
                    material.DeclarationStatementIds.Select(static declaration =>
                        new FrozenDeclaration(declaration.DeclarationNameKey, declaration.Kind)).ToImmutableArray());
                return new RepositoryFile(FrozenStatePath.FromModulePath(material.RepoPath), bytes,
                    Encoding.UTF8.GetString(bytes.AsSpan()));
            }).ToImmutableArray();

    internal static LeanAxiomReport Report(params ModuleSpec[] modules) => LeanAxiomReport.Create(
        modules.ToDictionary(module => PathFor(module.Name), module => new LeanFileReport(
            module.Imports.Select(ModuleNameFor).ToImmutableArray(),
            (module.Declarations.IsDefaultOrEmpty ? [module.Name.ToLowerInvariant()] : module.Declarations)
                .Select(name => new LeanDeclaration(name, module.Kind, module.StatementMaterial, module.Axioms)
                {
                    NameKey = module.OpaqueNameKeys ? NameKeyFor(name) : CanonicalNameKeyFor(name),
                    IncludeInStatement = module.Excluded.IsDefaultOrEmpty || !module.Excluded.Contains(name),
                }).ToImmutableArray()), StringComparer.Ordinal));

    internal static void AddLedgerFiles(
        IDictionary<string, string> files,
        IEnumerable<RepositoryFile> events)
    {
        foreach (var item in events)
        {
            files[item.Path.Value] = item.Text;
        }
    }

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

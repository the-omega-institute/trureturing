using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class FrozenLedgerTestData
{
    internal static FrozenMaterialCatalog BuildCatalog(params ModuleSpec[] modules)
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
            ["lake-manifest.json"] = "{}\n",
        };
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
        foreach (var module in modules)
        {
            files[PathFor(module.Name)] = module.Source;
            reports[PathFor(module.Name)] = new LeanFileReport(
                module.Imports.Select(ModuleNameFor).ToImmutableArray(),
                ImmutableArray.Create(new LeanDeclaration(
                    module.Name.ToLowerInvariant(),
                    "theorem",
                    "True",
                    module.Axioms)
                {
                    NameKey = $"ns(n0,{module.Name.Length}:{module.Name.ToLowerInvariant()})",
                }));
        }

        var raw = RawRepositorySnapshot.Create(
            files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
        var dag = Assert.IsType<DagBuildOutcome.Accepted>(AcyclicTruthDag.Build(snapshot, closure)).Capability;
        var environment = new FrozenEnvironmentAttestation(
            GitOid('a'),
            GitOid('b'),
            GitBlobOid(files["lean-toolchain"]),
            GitBlobOid(files["lake-manifest.json"]));
        var attestations = modules.Select(module => new FrozenModuleAttestation(
            RepoPathFor(module.Name),
            GitBlobOid(module.Source))
        {
            BaseCommitOid = module.BaseCommitOid,
            BaseTreeOid = module.BaseTreeOid,
        });

        return Assert.IsType<FrozenMaterialOutcome.Accepted>(
            FrozenContentAddress.Build(snapshot, closure, dag, environment, attestations)).Capability;
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
        var dag = Assert.IsType<DagBuildOutcome.Accepted>(AcyclicTruthDag.Build(snapshot, closure)).Capability;
        var environment = new FrozenEnvironmentAttestation(
            GitOid('a'),
            GitOid('b'),
            GitBlobOid(files["lean-toolchain"]),
            GitBlobOid(files["lake-manifest.json"]));
        return FrozenContentAddress.Build(
            snapshot,
            closure,
            dag,
            environment,
            Array.Empty<FrozenModuleAttestation>());
    }

    internal static ModuleSpec Module(
        string name,
        string? source = null,
        IReadOnlyList<string>? imports = null,
        IEnumerable<string>? axioms = null,
        string? baseCommitOid = null,
        string? baseTreeOid = null) =>
        new(
            name,
            source ?? $"theorem {name.ToLowerInvariant()} : True := by trivial\n",
            imports ?? Array.Empty<string>(),
            (axioms ?? Array.Empty<string>()).Order(StringComparer.Ordinal).ToImmutableArray(),
            baseCommitOid,
            baseTreeOid);

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

    private static string ModuleNameFor(string module) => $"D5.S0.Carrier.{module}";

    internal sealed record ModuleSpec(
        string Name,
        string Source,
        IReadOnlyList<string> Imports,
        ImmutableArray<string> Axioms,
        string? BaseCommitOid,
        string? BaseTreeOid);
}

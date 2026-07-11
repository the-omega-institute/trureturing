using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

public static class FrozenContentAddress
{
    private static readonly Regex CaseReferencePattern = new(
        "(?<![A-Za-z0-9_])D5-T[0-9]{4}(?![A-Za-z0-9_])",
        RegexOptions.CultureInvariant);

    private static readonly Regex AssumptionReferencePattern = new(
        "(?<![A-Za-z0-9_])D5/X_Assumptions/[A-Za-z0-9_/.-]+",
        RegexOptions.CultureInvariant);

    public static FrozenMaterialOutcome Build(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        AcyclicTruthDag dag,
        FrozenEnvironmentAttestation environment,
        IEnumerable<FrozenModuleAttestation> moduleAttestations)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(dag);
        ArgumentNullException.ThrowIfNull(environment);
        ArgumentNullException.ThrowIfNull(moduleAttestations);

        try
        {
            ValidateEnvironment(snapshot, environment);
            var (openCases, tailRegistrations) = ValidateStateEvidence(snapshot, lean, dag);
            var attestations = moduleAttestations.ToArray();
            var byPath = attestations.ToDictionary(static item => item.RepoPath);
            if (byPath.Count != attestations.Length)
            {
                throw new FormatException("Module attestations contain a duplicate path.");
            }

            var materialByPath = new Dictionary<RepoPath, FrozenNodeMaterial>();
            foreach (var node in dag.TopologicalOrder.Where(static node => node.State is TruthState.Closed))
            {
                if (!byPath.TryGetValue(node.RepoPath, out var attestation)
                    || !snapshot.Files.TryGetValue(node.RepoPath, out var source)
                    || !lean.Report.Files.TryGetValue(node.RepoPath, out var report))
                {
                    throw new FormatException($"Closed module {node.RepoPath.Value} has no complete attestation material.");
                }

                ValidateGitBlobOid(attestation.SourceBlobOid, source.RawBytes.AsSpan(), node.RepoPath.Value);
                if (attestation.BaseCommitOid is not null && !FrozenHashSyntax.IsGitOid(attestation.BaseCommitOid)
                    || attestation.BaseTreeOid is not null && !FrozenHashSyntax.IsGitOid(attestation.BaseTreeOid)
                    || (attestation.BaseCommitOid is null) != (attestation.BaseTreeOid is null))
                {
                    throw new FormatException(
                        $"Closed module {node.RepoPath.Value} has a malformed event-specific Git attestation.");
                }
                var declarationStatementIds = CanonicalStatementWriter.DeclarationStatementIds(
                    node.RepoPath,
                    report);
                var statement = StatementId.Create(FrozenContentHash.Compute(
                    FrozenHashDomains.Statement,
                    CanonicalStatementWriter.WriteModule(node.RepoPath, declarationStatementIds).AsSpan()));
                var witness = WitnessId.Create(FrozenContentHash.Compute(
                    FrozenHashDomains.Witness,
                    WriteWitness(node.RepoPath, statement, report, source, environment, attestation).AsSpan()));
                var axiomClosure = report.Declarations
                    .SelectMany(static declaration => declaration.Axioms)
                    .Distinct(StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal)
                    .ToImmutableArray();
                var prerequisites = dag.DependenciesOf(node.RepoPath)
                    .Select(path => materialByPath.TryGetValue(path, out var dependency)
                        ? dependency.FrozenNodeId
                        : throw new FormatException(
                            $"Closed module {node.RepoPath.Value} depends on non-frozen {path.Value}."))
                    .OrderBy(static id => id.Value, StringComparer.Ordinal)
                    .ToImmutableArray();
                var frozen = FrozenNodeId.Create(FrozenContentHash.Compute(
                    FrozenHashDomains.FrozenNode,
                    WriteFrozenNode(node.RepoPath, statement, witness, prerequisites).AsSpan()));
                materialByPath.Add(node.RepoPath, new FrozenNodeMaterial(
                    node.RepoPath,
                    declarationStatementIds,
                    statement,
                    witness,
                    frozen,
                    prerequisites,
                    axiomClosure,
                    attestation));
            }

            var unused = byPath.Keys
                .Where(path => !materialByPath.ContainsKey(path))
                .OrderBy(static path => path.Value, StringComparer.Ordinal)
                .ToArray();
            if (unused.Length > 0)
            {
                throw new FormatException(
                    "Attestations were supplied for non-Closed modules: "
                    + string.Join(", ", unused.Select(static path => path.Value)));
            }

            return new FrozenMaterialOutcome.Accepted(FrozenMaterialCatalog.Create(
                dag,
                environment,
                materialByPath.Values
                    .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
                    .ToImmutableArray(),
                openCases,
                tailRegistrations));
        }
        catch (Exception exception) when (exception is FormatException or ArgumentException)
        {
            return new FrozenMaterialOutcome.Rejected(exception.Message);
        }
    }

    private static void ValidateEnvironment(
        RepositorySnapshot snapshot,
        FrozenEnvironmentAttestation environment)
    {
        if (!FrozenHashSyntax.IsGitOid(environment.OriginCommitOid)
            || !FrozenHashSyntax.IsGitOid(environment.OriginTreeOid)
            || !snapshot.TryGetFile("lean-toolchain", out var toolchain)
            || !snapshot.TryGetFile("lake-manifest.json", out var manifest))
        {
            throw new FormatException("Frozen environment attestation is incomplete or malformed.");
        }

        ValidateGitBlobOid(environment.LeanToolchainBlobOid, toolchain.RawBytes.AsSpan(), "lean-toolchain");
        ValidateGitBlobOid(environment.LakeManifestBlobOid, manifest.RawBytes.AsSpan(), "lake-manifest.json");
    }

    private static (
        ImmutableDictionary<RepoPath, ImmutableArray<CaseId>> OpenCases,
        ImmutableDictionary<RepoPath, ImmutableArray<string>> TailRegistrations) ValidateStateEvidence(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        AcyclicTruthDag dag)
    {
        var openCases = ImmutableDictionary.CreateBuilder<RepoPath, ImmutableArray<CaseId>>();
        var tailRegistrations = ImmutableDictionary.CreateBuilder<RepoPath, ImmutableArray<string>>();
        foreach (var node in dag.Nodes.Where(static node => node.ModuleName is not null))
        {
            var source = snapshot.Files[node.RepoPath];
            if (node.State is TruthState.Open)
            {
                var cases = CaseReferencePattern.Matches(source.Text)
                    .Select(static match => CaseId.TryCreate(match.Value, out var caseId)
                        ? caseId
                        : throw new FormatException("Open module contains a malformed CaseId."))
                    .Distinct()
                    .OrderBy(static caseId => caseId.Value, StringComparer.Ordinal)
                    .ToImmutableArray();
                if (cases.Length == 0)
                {
                    throw new FormatException($"Open module {node.RepoPath.Value} has no permanent CaseId reference.");
                }

                openCases.Add(node.RepoPath, cases);
                continue;
            }

            if (node.State is not TruthState.Tail)
            {
                continue;
            }

            var report = lean.Report.Files[node.RepoPath];
            var registrations = report.Imports
                .Where(static module => module.StartsWith("D5.X_Assumptions.", StringComparison.Ordinal))
                .Select(static module => module.Replace('.', '/'))
                .Concat(AssumptionReferencePattern.Matches(source.Text).Select(static match => match.Value))
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray();
            if (registrations.Length == 0
                && node.RepoPath.Value.StartsWith("D5/X_Assumptions/", StringComparison.Ordinal)
                && snapshot.TryGetFile("D5/X_Assumptions/REGISTRY.md", out var registry))
            {
                var gid = node.RepoPath.Value.EndsWith(".lean", StringComparison.Ordinal)
                    ? node.RepoPath.Value[..^5]
                    : node.RepoPath.Value;
                if (registry.Text.Contains(gid, StringComparison.Ordinal))
                {
                    registrations = ImmutableArray.Create(gid);
                }
            }

            if (registrations.Length == 0)
            {
                throw new FormatException(
                    $"Tail module {node.RepoPath.Value} has no X_Assumptions registration reference.");
            }

            tailRegistrations.Add(node.RepoPath, registrations);
        }

        return (openCases.ToImmutable(), tailRegistrations.ToImmutable());
    }

    private static ImmutableArray<byte> WriteWitness(
        RepoPath path,
        StatementId statement,
        LeanFileReport report,
        RepositoryFile source,
        FrozenEnvironmentAttestation environment,
        FrozenModuleAttestation attestation)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            axiom_closure = report.Declarations
                .SelectMany(static declaration => declaration.Axioms)
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal),
            imports = report.Imports.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal),
            lake_manifest_blob_oid = environment.LakeManifestBlobOid,
            lean_toolchain_blob_oid = environment.LeanToolchainBlobOid,
            module_path = path.Value,
            schema = "witness-v1",
            source_blob_oid = attestation.SourceBlobOid,
            source_sha256 = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(source.RawBytes.AsSpan())),
            statement_id = statement.Value,
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    private static ImmutableArray<byte> WriteFrozenNode(
        RepoPath path,
        StatementId statement,
        WitnessId witness,
        ImmutableArray<FrozenNodeId> prerequisites)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            module_path = path.Value,
            prerequisite_frozen_node_ids = prerequisites.Select(static id => id.Value),
            schema = "frozen-node-v1",
            statement_id = statement.Value,
            witness_id = witness.Value,
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    internal static void ValidateGitBlobOid(string oid, ReadOnlySpan<byte> bytes, string label)
    {
        if (!FrozenHashSyntax.IsGitOid(oid))
        {
            throw new FormatException($"{label} has a malformed Git blob OID.");
        }

        var header = Encoding.ASCII.GetBytes($"blob {bytes.Length}\0");
        byte[] actual;
        if (oid.StartsWith("git-sha1:", StringComparison.Ordinal))
        {
            using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA1);
            hash.AppendData(header);
            hash.AppendData(bytes);
            actual = hash.GetHashAndReset();
        }
        else
        {
            using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
            hash.AppendData(header);
            hash.AppendData(bytes);
            actual = hash.GetHashAndReset();
        }

        var expected = oid[(oid.IndexOf(':') + 1)..];
        if (!string.Equals(Convert.ToHexStringLower(actual), expected, StringComparison.Ordinal))
        {
            throw new FormatException($"{label} Git blob OID does not match its source bytes.");
        }
    }

    internal static string ComputeGitBlobOid(ReadOnlySpan<byte> bytes, HashAlgorithmName algorithm)
    {
        var header = Encoding.ASCII.GetBytes($"blob {bytes.Length}\0");
        using var hash = IncrementalHash.CreateHash(algorithm);
        hash.AppendData(header);
        hash.AppendData(bytes);
        var prefix = algorithm == HashAlgorithmName.SHA1 ? "git-sha1:" : "git-sha256:";
        return prefix + Convert.ToHexStringLower(hash.GetHashAndReset());
    }
}

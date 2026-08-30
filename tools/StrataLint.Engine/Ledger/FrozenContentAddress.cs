using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using Trureturing.Truth;

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
        ImmutableDictionary<RepoPath, TruthState> states,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(states);
        ArgumentNullException.ThrowIfNull(adjacency);

        try
        {
            var (openCases, tailRegistrations) = ValidateStateEvidence(snapshot, lean, states);
            var materialByPath = new Dictionary<RepoPath, FrozenNodeMaterial>();
            foreach (var path in LeanImportAdjacency.DependenciesFirst(
                states.Where(static item => item.Value is TruthState.Closed).Select(static item => item.Key),
                adjacency).Where(path => states.TryGetValue(path, out var state)
                    && state is TruthState.Closed))
            {
                materialByPath.Add(
                    path,
                    BuildNodeMaterial(
                        lean,
                        adjacency,
                        path,
                        dependencyPath => materialByPath.TryGetValue(dependencyPath, out var dependency)
                            ? dependency.FrozenNodeId
                            : throw new FormatException(
                                $"Closed module {path.Value} depends on non-frozen {dependencyPath.Value}.")));
            }

            return new FrozenMaterialOutcome.Accepted(FrozenMaterialCatalog.Create(
                states.ToImmutableDictionary(),
                materialByPath.Values
                    .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
                    .ToImmutableArray(),
                openCases,
                tailRegistrations,
                adjacency));
        }
        catch (Exception exception) when (exception is FormatException or ArgumentException)
        {
            return new FrozenMaterialOutcome.Rejected(exception.Message);
        }
    }

    internal static FrozenMaterialCatalog BuildAdmissionCatalog(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        ImmutableDictionary<RepoPath, TruthState> states,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency,
        IReadOnlySet<RepoPath> selectedPaths,
        IReadOnlyDictionary<RepoPath, FrozenNodeMaterial> trustedBaseMaterials)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(states);
        ArgumentNullException.ThrowIfNull(adjacency);
        ArgumentNullException.ThrowIfNull(selectedPaths);
        ArgumentNullException.ThrowIfNull(trustedBaseMaterials);
        var materialByPath = new Dictionary<RepoPath, FrozenNodeMaterial>();
        foreach (var path in LeanImportAdjacency.DependenciesFirst(selectedPaths, adjacency)
            .Where(path => states.TryGetValue(path, out var state)
                && state is TruthState.Closed
                && selectedPaths.Contains(path)))
        {
            materialByPath.Add(
                path,
                BuildNodeMaterial(
                    lean,
                    adjacency,
                    path,
                    dependencyPath => trustedBaseMaterials.TryGetValue(dependencyPath, out var trustedDependency)
                            ? trustedDependency.FrozenNodeId
                        : materialByPath.TryGetValue(dependencyPath, out var selectedDependency)
                            ? selectedDependency.FrozenNodeId
                            : throw new FormatException(
                                $"Selected Closed module {path.Value} depends on unrecorded {dependencyPath.Value}.")));
        }

        return FrozenMaterialCatalog.Create(
            states.ToImmutableDictionary(),
            materialByPath.Values
                .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
                .ToImmutableArray(),
            ImmutableDictionary<RepoPath, ImmutableArray<CaseId>>.Empty,
            ImmutableDictionary<RepoPath, ImmutableArray<string>>.Empty,
            adjacency);
    }

    private static FrozenNodeMaterial BuildNodeMaterial(
        AcceptedLeanClosure lean,
        IReadOnlyDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency,
        RepoPath path,
        Func<RepoPath, FrozenNodeId> resolveDependency)
    {
        if (!lean.Report.Files.TryGetValue(path, out var report))
        {
            throw new FormatException($"Closed module {path.Value} has no Lean report material.");
        }

        var declarationStatementIds = CanonicalStatementWriter.DeclarationStatementIds(
            path,
            report);
        var statement = StatementId.Create(FrozenContentHash.Compute(
            FrozenHashDomains.Statement,
            CanonicalStatementWriter.WriteModule(path, declarationStatementIds).AsSpan()));
        var axiomClosure = report.Declarations
            .SelectMany(static declaration => declaration.Axioms)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var prerequisites = adjacency[path]
            .Select(resolveDependency)
            .OrderBy(static id => id.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var frozen = ComputeFrozenNodeId(path, statement, prerequisites);
        return new FrozenNodeMaterial(
            path,
            declarationStatementIds,
            statement,
            frozen,
            prerequisites,
            axiomClosure);
    }

    private static (
        ImmutableDictionary<RepoPath, ImmutableArray<CaseId>> OpenCases,
        ImmutableDictionary<RepoPath, ImmutableArray<string>> TailRegistrations) ValidateStateEvidence(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        IReadOnlyDictionary<RepoPath, TruthState> states)
    {
        var openCases = ImmutableDictionary.CreateBuilder<RepoPath, ImmutableArray<CaseId>>();
        var tailRegistrations = ImmutableDictionary.CreateBuilder<RepoPath, ImmutableArray<string>>();
        foreach (var (path, state) in states.OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
        {
            var source = snapshot.Files[path];
            if (state is TruthState.Open)
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
                    throw new FormatException($"Open module {path.Value} has no permanent CaseId reference.");
                }

                openCases.Add(path, cases);
                continue;
            }

            if (state is not TruthState.Tail)
            {
                continue;
            }

            var report = lean.Report.Files[path];
            var registrations = report.Imports
                .Where(static module => module.StartsWith("D5.X_Assumptions.", StringComparison.Ordinal))
                .Select(static module => module.Replace('.', '/'))
                .Concat(AssumptionReferencePattern.Matches(source.Text).Select(static match => match.Value))
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray();
            if (registrations.Length == 0
                && path.Value.StartsWith("D5/X_Assumptions/", StringComparison.Ordinal)
                && snapshot.TryGetFile(RepositoryPathPolicy.AssumptionRegistryPath, out var registry))
            {
                var gid = path.Value.EndsWith(".lean", StringComparison.Ordinal)
                    ? path.Value[..^5]
                    : path.Value;
                if (registry.Text.Contains(gid, StringComparison.Ordinal))
                {
                    registrations = ImmutableArray.Create(gid);
                }
            }

            if (registrations.Length == 0)
            {
                throw new FormatException(
                    $"Tail module {path.Value} has no X_Assumptions registration reference.");
            }

            tailRegistrations.Add(path, registrations);
        }

        return (openCases.ToImmutable(), tailRegistrations.ToImmutable());
    }

    internal static FrozenNodeId ComputeFrozenNodeId(
        RepoPath path,
        StatementId statement,
        ImmutableArray<FrozenNodeId> prerequisites)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            module_path = path.Value,
            prerequisite_frozen_node_ids = prerequisites.Select(static id => id.Value),
            schema = "frozen-node-v2",
            statement_id = statement.Value,
        });
        return FrozenNodeId.Create(FrozenContentHash.Compute(
            FrozenHashDomains.FrozenNode,
            StructuredCanonicalWriter.WriteJson(material).AsSpan()));
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

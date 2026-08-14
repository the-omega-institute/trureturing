using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record FrozenEnvironmentRecoordinateGeneration(
    ImmutableArray<byte> Bytes,
    ImmutableArray<RepoPath> RecoordinatedPaths,
    ImmutableArray<RepoPath> ReattestPaths);

public static partial class FrozenLedgerGenerator
{
    internal static FrozenEnvironmentRecoordinateGeneration AppendEnvironmentRecoordinates(
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog candidateCatalog,
        LeanAxiomReport candidateReport,
        RepositorySnapshot candidateSnapshot,
        LeanAxiomReport oldReport,
        RepositorySnapshot oldSnapshot,
        FrozenEnvironmentPins oldEnvironment)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(candidateCatalog);
        ArgumentNullException.ThrowIfNull(candidateReport);
        ArgumentNullException.ThrowIfNull(candidateSnapshot);
        ArgumentNullException.ThrowIfNull(oldReport);
        ArgumentNullException.ThrowIfNull(oldSnapshot);
        ArgumentNullException.ThrowIfNull(oldEnvironment);

        var newEnvironment = EnvironmentPins(candidateCatalog.Environment);
        if (oldEnvironment == newEnvironment)
        {
            throw new InvalidOperationException(
                "EnvironmentRecoordinate requires distinct old and new environments.");
        }

        var payloads = ImmutableArray.CreateBuilder<(string Type, JsonElement Payload)>();
        var recoordinated = ImmutableArray.CreateBuilder<RepoPath>();
        var reattest = ImmutableArray.CreateBuilder<RepoPath>();
        foreach (var entry in baseline.ActiveEntries.Values.OrderBy(
            static item => item.Material.RepoPath.Value,
            StringComparer.Ordinal))
        {
            var path = entry.Material.RepoPath;
            if (!candidateCatalog.ByPath.TryGetValue(path, out var candidate)
                || !candidateReport.Files.TryGetValue(path, out var candidateFile)
                || !candidateSnapshot.Files.TryGetValue(path, out var candidateSource))
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} has no candidate Closed material or Lean report.");
            }

            if (entry.Material.FrozenNodeId == candidate.FrozenNodeId
                && entry.Environment is { } activeEnvironment
                && activeEnvironment == newEnvironment)
            {
                continue;
            }

            if (entry.Material.Attestation.SourceBlobOid != candidate.Attestation.SourceBlobOid)
            {
                reattest.Add(path);
                continue;
            }

            if (!oldReport.Files.TryGetValue(path, out var oldFile)
                || !oldSnapshot.Files.TryGetValue(path, out var oldSource))
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} has no old Lean report or source material.");
            }

            if (!oldSource.RawBytes.AsSpan().SequenceEqual(candidateSource.RawBytes.AsSpan()))
            {
                throw new InvalidOperationException(
                    $"Old and candidate source bytes differ for {path.Value} despite a stable source blob OID.");
            }

            var oldDeclarations = CanonicalStatementWriter.DeclarationStatementIds(path, oldFile);
            var oldStatement = StatementId.Create(FrozenContentHash.Compute(
                FrozenHashDomains.Statement,
                CanonicalStatementWriter.WriteModule(path, oldDeclarations).AsSpan()));
            if (!oldDeclarations.SequenceEqual(entry.Material.DeclarationStatementIds)
                || oldStatement != entry.Material.StatementId)
            {
                throw new InvalidOperationException(
                    $"Old Lean report statement coordinates do not match active material for {path.Value}.");
            }

            var oldImports = CanonicalStrings(oldFile.Imports);
            var newImports = CanonicalStrings(candidateFile.Imports);
            var oldAxiomClosure = CanonicalStrings(
                oldFile.Declarations.SelectMany(static declaration => declaration.Axioms));
            var sourceSha256 = "sha256:"
                + Convert.ToHexStringLower(
                    System.Security.Cryptography.SHA256.HashData(oldSource.RawBytes.AsSpan()));
            var oldWitness = FrozenContentAddress.ComputeWitnessId(
                path,
                entry.Material.StatementId,
                oldImports,
                oldAxiomClosure,
                entry.Material.Attestation.SourceBlobOid,
                sourceSha256,
                oldEnvironment.LeanToolchainBlobOid,
                oldEnvironment.LakeManifestBlobOid);
            var oldFrozen = FrozenContentAddress.ComputeFrozenNodeId(
                path,
                entry.Material.StatementId,
                oldWitness,
                entry.Material.PrerequisiteFrozenNodeIds);
            if (oldWitness != entry.Material.WitnessId
                || oldFrozen != entry.Material.FrozenNodeId)
            {
                throw new InvalidOperationException(
                    $"Old Lean report imports/axiom closure do not match active addresses for {path.Value}.");
            }

            var payload = new FrozenEnvironmentRecoordinatePayload(
                entry.Payload.CaseId,
                candidate.DeclarationStatementIds,
                entry.Material.DeclarationStatementIds,
                newEnvironment,
                oldEnvironment,
                FrozenLedger.EnvironmentRecoordinateUnprovedEquivalence,
                nameof(TruthState.Closed),
                candidate.AxiomClosure,
                candidate.FrozenNodeId,
                newImports,
                EnvironmentInput(candidateCatalog.Environment, candidate, newEnvironment),
                candidate.PrerequisiteFrozenNodeIds,
                candidate.StatementId,
                candidate.WitnessId,
                oldAxiomClosure,
                entry.Material.FrozenNodeId,
                oldImports,
                entry.Payload.Input with
                {
                    SupportingBlobOids = EnvironmentPinOids(oldEnvironment),
                },
                entry.Material.PrerequisiteFrozenNodeIds,
                entry.Material.StatementId,
                entry.Material.WitnessId,
                entry.LastAttestationEventHash,
                sourceSha256);
            payloads.Add((
                FrozenLedger.EnvironmentRecoordinateEventType,
                FrozenLedgerCanonicalWriter.EnvironmentRecoordinateElement(payload)));
            recoordinated.Add(path);
        }

        return new FrozenEnvironmentRecoordinateGeneration(
            Append(baseline, payloads.ToImmutable()),
            recoordinated.ToImmutable(),
            reattest.ToImmutable());
    }

    private static ImmutableArray<string> CanonicalStrings(IEnumerable<string> values) =>
        values.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();

    private static FrozenLedgerInput EnvironmentInput(
        FrozenEnvironmentAttestation environment,
        FrozenNodeMaterial material,
        FrozenEnvironmentPins pins) =>
        new(
            material.Attestation.BaseCommitOid ?? environment.OriginCommitOid,
            material.Attestation.BaseTreeOid ?? environment.OriginTreeOid,
            material.Attestation.SourceBlobOid,
            material.RepoPath.Value,
            "repository-snapshot-v1",
            EnvironmentPinOids(pins));

    private static FrozenEnvironmentPins EnvironmentPins(
        FrozenEnvironmentAttestation environment)
    {
        if (environment.LakefilePath is null || environment.LakefileBlobOid is null)
        {
            throw new InvalidOperationException(
                "EnvironmentRecoordinate requires exactly one pinned lakefile.toml or lakefile.lean.");
        }

        return new FrozenEnvironmentPins(
            environment.LakeManifestBlobOid,
            environment.LakefileBlobOid,
            RepoPath.CreateKnown(environment.LakefilePath),
            environment.LeanToolchainBlobOid);
    }

    private static ImmutableArray<string> EnvironmentPinOids(FrozenEnvironmentPins environment) =>
        new[]
        {
            environment.LakeManifestBlobOid,
            environment.LakefileBlobOid,
            environment.LeanToolchainBlobOid,
        }.Order(StringComparer.Ordinal).ToImmutableArray();
}

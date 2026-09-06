using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestionReceiptBuilder
{
    internal static (DigestionCoverageEdge Coverage, DigestionScribeReceipt Scribe) Build(
        Gid gid,
        RepositorySnapshot snapshot,
        FrozenStatementIndex frozenStatements,
        VerifiedScribeEmissions verifiedScribeEmissions)
    {
        if (!snapshot.TryGetFile(gid.Path.Value, out _))
        {
            throw new InvalidOperationException($"cover target Lean file is absent: {gid.Path.Value}");
        }

        if (!frozenStatements.TryResolve(gid, out var targetStatementId, out var resolutionError))
        {
            throw new InvalidOperationException(
                $"cover target has no unique frozen statement: {gid.Value} ({resolutionError})");
        }

        var documentGid = ScribeEmissionAttestation.DocumentGid(gid.Value);
        if (!verifiedScribeEmissions.TryGet(documentGid, out var verifiedRecord))
        {
            throw new InvalidOperationException(
                $"cover verified Scribe emission is absent: {documentGid} "
                + "(scribe-emission-missing; partial-closed)");
        }

        var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
        if (!snapshot.TryGetFile(definitionPath, out var definition))
        {
            throw new InvalidOperationException($"cover Scribe definition is absent: {definitionPath}");
        }

        return (new DigestionCoverageEdge(gid.Value, targetStatementId!.Value),
            new DigestionScribeReceipt(gid.Value,
                DigestionFingerprint.Compute(definition.RawBytes.AsSpan()).RawSha256,
                verifiedRecord.EmissionSha256));
    }
}

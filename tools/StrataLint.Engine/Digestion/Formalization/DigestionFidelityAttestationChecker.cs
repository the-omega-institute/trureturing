namespace StrataLint.Engine;

internal sealed record DigestionFidelityAttestationEvaluation(
    int ClauseCount,
    int UndischargedCount,
    int FailedGraderTrapCount);

internal static class DigestionFidelityAttestationChecker
{
    internal static DigestionFidelityAttestationEvaluation Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        string relativePath)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(report);
        var attestation = DigestionFidelityAttestation.Load(snapshot, relativePath);
        var document = BackfillInventoryLoader.Load(snapshot);
        var entries = document.RequireDigestionEntries()
            .Where(entry => string.Equals(entry.AtomId, attestation.AtomId, StringComparison.Ordinal))
            .ToArray();
        if (entries.Length != 1)
        {
            throw new FormatException(entries.Length == 0
                ? $"fidelity attestation atom {attestation.AtomId} is absent from the ledger"
                : $"fidelity attestation atom {attestation.AtomId} is ambiguous in the ledger");
        }

        var entry = entries[0];
        if (!string.Equals(entry.CasRef, attestation.SourceSha256, StringComparison.Ordinal)
            || !string.Equals(
                entry.Fingerprints.RawSha256,
                attestation.SourceSha256,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                $"fidelity attestation source hash does not match live atom {attestation.AtomId}");
        }

        var casPath = DigestionCasStore.RootPath
            + attestation.SourceSha256["sha256:".Length..];
        if (!snapshot.TryGetFile(casPath, out var casBlob))
        {
            throw new FormatException($"fidelity attestation source CAS blob is missing: {casPath}");
        }

        var actualSourceSha256 = DigestionFingerprint.Compute(casBlob.RawBytes.AsSpan()).RawSha256;
        if (!string.Equals(actualSourceSha256, attestation.SourceSha256, StringComparison.Ordinal))
        {
            throw new FormatException(
                $"fidelity attestation source CAS hash mismatch: {casPath}");
        }

        foreach (var clause in attestation.Clauses)
        {
            if (clause.EndByte > casBlob.RawBytes.Length)
            {
                throw new FormatException(
                    $"fidelity attestation clause {clause.Key} span exceeds the pinned source");
            }

            var bytes = casBlob.RawBytes.AsSpan()[clause.StartByte..clause.EndByte];
            var actualClauseSha256 = DigestionFingerprint.Compute(bytes).RawSha256;
            if (!string.Equals(actualClauseSha256, clause.ClauseSha256, StringComparison.Ordinal))
            {
                throw new FormatException(
                    $"fidelity attestation clause {clause.Key} hash does not match its source span");
            }
        }

        var theorem = ResolveDeclaration(attestation.TheoremGid, report);
        var theoremGid = Gid.TryParse(attestation.TheoremGid, out var parsedTheorem)
            ? parsedTheorem
            : throw new FormatException(
                $"fidelity attestation theorem GID is invalid: {attestation.TheoremGid}");
        var statement = CanonicalStatementWriter.DeclarationStatementIds(
            theoremGid.Path,
            new LeanFileReport([], [theorem]));
        if (statement.Length != 1
            || !string.Equals(
                statement[0].StatementId.Value,
                attestation.DeclarationSha256,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                $"fidelity attestation declaration hash does not match {attestation.TheoremGid}");
        }

        foreach (var mapping in attestation.ClauseMap
                     .Where(static item => item.Status is DigestionFidelityClauseStatus.Discharged))
        {
            _ = ResolveDeclaration(mapping.Gid!, report);
        }

        return new DigestionFidelityAttestationEvaluation(
            attestation.Clauses.Length,
            attestation.ClauseMap.Count(static item =>
                item.Status is DigestionFidelityClauseStatus.Undischarged),
            attestation.GraderTraps.Count(static item =>
                item.Result is DigestionFidelityGraderResult.Fail));
    }

    private static LeanDeclaration ResolveDeclaration(string gidText, LeanAxiomReport report)
    {
        if (!Gid.TryParse(gidText, out var gid)
            || gid.ToTarget() is not Target.Formal { Declaration: { } selector } formal
            || !report.Files.TryGetValue(formal.Path, out var module)
            || !string.IsNullOrEmpty(module.Error))
        {
            throw new FormatException(
                $"fidelity attestation GID is absent from the Lean report: {gidText}");
        }

        var suffix = "." + selector;
        var matches = module.Declarations
            .Where(candidate => string.Equals(candidate.Name, selector, StringComparison.Ordinal)
                || candidate.Name.EndsWith(suffix, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length != 1)
        {
            throw new FormatException(
                $"fidelity attestation GID {gidText} resolves to {matches.Length} declarations");
        }

        return matches[0];
    }
}

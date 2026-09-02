using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum DigestionFormalizationReceiptTransitionKind
{
    HostedAppend,
    SignatureReanchor,
    Rejected,
}

internal sealed record DigestionFormalizationReceiptTransitionResult(
    DigestionFormalizationReceiptTransitionKind Kind,
    string Clause,
    ImmutableArray<string> AffectedGids)
{
    internal static DigestionFormalizationReceiptTransitionResult HostedAppend(
        IEnumerable<string> addedGids) =>
        new(
            DigestionFormalizationReceiptTransitionKind.HostedAppend,
            string.Empty,
            addedGids.Order(StringComparer.Ordinal).ToImmutableArray());

    internal static DigestionFormalizationReceiptTransitionResult SignatureReanchor(
        IEnumerable<string> changedGids) =>
        new(
            DigestionFormalizationReceiptTransitionKind.SignatureReanchor,
            string.Empty,
            changedGids.Order(StringComparer.Ordinal).ToImmutableArray());

    internal static DigestionFormalizationReceiptTransitionResult Rejected(string clause) =>
        new(
            DigestionFormalizationReceiptTransitionKind.Rejected,
            clause,
            []);
}

internal sealed record DigestionFormalizationReceiptTransitionInput(
    DigestionFormalizationReceipt Baseline,
    DigestionFormalizationReceipt Candidate);

internal static class DigestionFormalizationReceiptTransition
{
    private sealed record Preliminary(
        DigestionFormalizationReceiptTransitionResult Result,
        ImmutableHashSet<RepoPath> ReanchoredPaths);

    internal static DigestionFormalizationReceiptTransitionResult Evaluate(
        DigestionFormalizationReceipt baseline,
        DigestionFormalizationReceipt candidate,
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidateSnapshot,
        LeanAxiomReport candidateReport) =>
        EvaluateBatch(
            [new DigestionFormalizationReceiptTransitionInput(baseline, candidate)],
            protectedBase,
            candidateSnapshot,
            candidateReport)[0];

    internal static ImmutableArray<DigestionFormalizationReceiptTransitionResult> EvaluateBatch(
        ImmutableArray<DigestionFormalizationReceiptTransitionInput> transitions,
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidateSnapshot,
        LeanAxiomReport candidateReport)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidateSnapshot);
        ArgumentNullException.ThrowIfNull(candidateReport);
        if (transitions.IsDefault)
        {
            throw new ArgumentException("receipt transition batch must be initialized", nameof(transitions));
        }

        var preliminary = transitions
            .Select(transition => EvaluateFields(transition, candidateReport))
            .ToImmutableArray();
        var allReanchoredPaths = preliminary
            .SelectMany(static item => item.ReanchoredPaths)
            .ToImmutableHashSet();
        if (allReanchoredPaths.IsEmpty)
        {
            return preliminary.Select(static item => item.Result).ToImmutableArray();
        }

        try
        {
            var baseView = FrozenLedgerBaseViewReader.Read(protectedBase);
            var lean = LeanClosureValidator.Validate(candidateSnapshot, candidateReport) switch
            {
                LeanValidationOutcome.Accepted accepted => accepted.Capability,
                LeanValidationOutcome.InfrastructureFailure failure => throw new FormatException(
                    failure.Message),
                _ => throw new InvalidOperationException("unknown Lean validation outcome"),
            };
            var states = LeanTruthStates.Resolve(candidateSnapshot, lean);
            var adjacency = LeanImportAdjacency.Build(candidateSnapshot, lean);
            var results = ImmutableArray.CreateBuilder<DigestionFormalizationReceiptTransitionResult>(
                preliminary.Length);
            foreach (var item in preliminary)
            {
                if (item.Result.Kind != DigestionFormalizationReceiptTransitionKind.SignatureReanchor)
                {
                    results.Add(item.Result);
                    continue;
                }

                string? sourceFailure = null;
                try
                {
                    var candidateCatalog = FrozenContentAddress.BuildAdmissionCatalog(
                        candidateSnapshot,
                        lean,
                        states,
                        adjacency,
                        item.ReanchoredPaths,
                        baseView.ActiveByPath);
                    if (!LeanPropositionSourceComparer.AreEquivalent(
                            protectedBase,
                            candidateSnapshot,
                            item.ReanchoredPaths,
                            baseView,
                            candidateCatalog))
                    {
                        sourceFailure = "Lean proposition source comparer returned false";
                    }
                }
                catch (Exception exception) when (exception is not OutOfMemoryException)
                {
                    sourceFailure = exception.Message;
                }

                results.Add(sourceFailure is null
                    ? item.Result
                    : RejectSource(item, sourceFailure));
            }

            return results.ToImmutable();
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return preliminary.Select(item =>
                item.Result.Kind == DigestionFormalizationReceiptTransitionKind.SignatureReanchor
                    ? RejectSource(item, exception.Message)
                    : item.Result).ToImmutableArray();
        }
    }

    private static DigestionFormalizationReceiptTransitionResult RejectSource(
        Preliminary item,
        string sourceFailure) =>
        DigestionFormalizationReceiptTransitionResult.Rejected(
            "reanchor requires equivalent Lean proposition source "
            + "(SignatureReanchor clause) for "
            + string.Join(
                ", ",
                item.ReanchoredPaths
                    .OrderBy(static path => path.Value, StringComparer.Ordinal)
                    .Select(static path => path.Value))
            + ": "
            + sourceFailure);

    private static Preliminary EvaluateFields(
        DigestionFormalizationReceiptTransitionInput transition,
        LeanAxiomReport candidateReport)
    {
        ArgumentNullException.ThrowIfNull(transition);
        ArgumentNullException.ThrowIfNull(transition.Baseline);
        ArgumentNullException.ThrowIfNull(transition.Candidate);
        var baseline = transition.Baseline;
        var candidate = transition.Candidate;

        var commonFailure = RequireCommonFields(baseline, candidate);
        if (commonFailure is not null)
        {
            return Reject(commonFailure);
        }

        var baselineExtensions = ExtensionsByGid(baseline, out var baselineExtensionFailure);
        if (baselineExtensionFailure is not null)
        {
            return Reject(baselineExtensionFailure);
        }

        var candidateExtensions = ExtensionsByGid(candidate, out var candidateExtensionFailure);
        if (candidateExtensionFailure is not null)
        {
            return Reject(candidateExtensionFailure);
        }

        var removed = baselineExtensions.Keys
            .Except(candidateExtensions.Keys, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        if (!removed.IsEmpty)
        {
            return Reject(
                "HostedAppend clause rejects an existing hosted extension that was removed or "
                + "replaced; if this is a legal flow, open a ticket citing #4710: "
                + string.Join(", ", removed));
        }

        var nameKeyFailure = RequireUnchangedNameKeys(
            baseline,
            candidate,
            baselineExtensions,
            candidateExtensions);
        if (nameKeyFailure is not null)
        {
            return Reject(nameKeyFailure);
        }

        var kindFailure = RequireUnchangedKinds(
            baseline,
            candidate,
            baselineExtensions,
            candidateExtensions);
        if (kindFailure is not null)
        {
            return Reject(kindFailure);
        }

        var addedGids = candidateExtensions.Keys
            .Except(baselineExtensions.Keys, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var changedTypes = ChangedTypeGids(
            baseline,
            candidate,
            baselineExtensions,
            candidateExtensions);
        if (!addedGids.IsEmpty && !changedTypes.IsEmpty)
        {
            return Reject(
                "variant exclusivity clause rejects a mixed transition that both appends hosted "
                + "extensions and reanchors an existing signature type");
        }

        if (!addedGids.IsEmpty)
        {
            foreach (var gid in addedGids)
            {
                var signatureFailure = RequireCandidateReportSignature(
                    gid,
                    candidateExtensions[gid].Signature,
                    candidateReport);
                if (signatureFailure is not null)
                {
                    return Reject(signatureFailure);
                }
            }

            return new Preliminary(
                DigestionFormalizationReceiptTransitionResult.HostedAppend(addedGids),
                ImmutableHashSet<RepoPath>.Empty);
        }

        if (changedTypes.IsEmpty)
        {
            return new Preliminary(
                DigestionFormalizationReceiptTransitionResult.HostedAppend([]),
                ImmutableHashSet<RepoPath>.Empty);
        }

        var reanchoredPaths = ImmutableHashSet.CreateBuilder<RepoPath>();
        foreach (var (gid, signature) in CandidateSignatures(candidate))
        {
            var signatureFailure = RequireCandidateReportSignature(
                gid,
                signature,
                candidateReport);
            if (signatureFailure is not null)
            {
                return Reject(signatureFailure);
            }

            if (changedTypes.Contains(gid)
                && Gid.TryParse(gid, out var parsed))
            {
                reanchoredPaths.Add(parsed.Path);
            }
        }

        return new Preliminary(
            DigestionFormalizationReceiptTransitionResult.SignatureReanchor(changedTypes),
            reanchoredPaths.ToImmutable());
    }

    private static string? RequireCommonFields(
        DigestionFormalizationReceipt baseline,
        DigestionFormalizationReceipt candidate)
    {
        if (!string.Equals(baseline.AtomId, candidate.AtomId, StringComparison.Ordinal))
        {
            return "reanchor requires unchanged atom_id";
        }

        if (!string.Equals(baseline.CasRef, candidate.CasRef, StringComparison.Ordinal))
        {
            return "reanchor requires unchanged cas_ref";
        }

        if (!string.Equals(baseline.RawSha256, candidate.RawSha256, StringComparison.Ordinal))
        {
            return "reanchor requires unchanged raw_sha256";
        }

        return string.Equals(baseline.PrimaryGid, candidate.PrimaryGid, StringComparison.Ordinal)
            ? null
            : "transition common clause requires unchanged primary_gid";
    }

    private static ImmutableDictionary<string, DigestionFormalizationExtension> ExtensionsByGid(
        DigestionFormalizationReceipt receipt,
        out string? failure)
    {
        var extensions = receipt.HostedExtensions.IsDefault ? [] : receipt.HostedExtensions;
        var duplicate = extensions.GroupBy(static extension => extension.Gid, StringComparer.Ordinal)
            .FirstOrDefault(static group => group.Count() != 1);
        if (duplicate is not null)
        {
            failure = "HostedAppend clause requires every hosted GID to be unique: " + duplicate.Key;
            return ImmutableDictionary<string, DigestionFormalizationExtension>.Empty;
        }

        failure = null;
        return extensions.ToImmutableDictionary(static extension => extension.Gid, StringComparer.Ordinal);
    }

    private static string? RequireUnchangedNameKeys(
        DigestionFormalizationReceipt baseline,
        DigestionFormalizationReceipt candidate,
        ImmutableDictionary<string, DigestionFormalizationExtension> baselineExtensions,
        ImmutableDictionary<string, DigestionFormalizationExtension> candidateExtensions)
    {
        if (!string.Equals(
                baseline.Signature.NameKey,
                candidate.Signature.NameKey,
                StringComparison.Ordinal))
        {
            return "reanchor requires unchanged signature name_key for " + baseline.PrimaryGid;
        }

        foreach (var gid in baselineExtensions.Keys.Order(StringComparer.Ordinal))
        {
            if (!string.Equals(
                    baselineExtensions[gid].Signature.NameKey,
                    candidateExtensions[gid].Signature.NameKey,
                    StringComparison.Ordinal))
            {
                return "reanchor requires unchanged signature name_key for " + gid;
            }
        }

        return null;
    }

    private static string? RequireUnchangedKinds(
        DigestionFormalizationReceipt baseline,
        DigestionFormalizationReceipt candidate,
        ImmutableDictionary<string, DigestionFormalizationExtension> baselineExtensions,
        ImmutableDictionary<string, DigestionFormalizationExtension> candidateExtensions)
    {
        if (!string.Equals(
                baseline.Signature.Kind,
                candidate.Signature.Kind,
                StringComparison.Ordinal))
        {
            return "reanchor requires unchanged signature kind for " + baseline.PrimaryGid;
        }

        foreach (var gid in baselineExtensions.Keys.Order(StringComparer.Ordinal))
        {
            if (!string.Equals(
                    baselineExtensions[gid].Signature.Kind,
                    candidateExtensions[gid].Signature.Kind,
                    StringComparison.Ordinal))
            {
                return "reanchor requires unchanged signature kind for " + gid;
            }
        }

        return null;
    }

    private static ImmutableHashSet<string> ChangedTypeGids(
        DigestionFormalizationReceipt baseline,
        DigestionFormalizationReceipt candidate,
        ImmutableDictionary<string, DigestionFormalizationExtension> baselineExtensions,
        ImmutableDictionary<string, DigestionFormalizationExtension> candidateExtensions)
    {
        var changed = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        if (!string.Equals(
                baseline.Signature.Type,
                candidate.Signature.Type,
                StringComparison.Ordinal))
        {
            changed.Add(baseline.PrimaryGid);
        }

        foreach (var gid in baselineExtensions.Keys)
        {
            if (!string.Equals(
                    baselineExtensions[gid].Signature.Type,
                    candidateExtensions[gid].Signature.Type,
                    StringComparison.Ordinal))
            {
                changed.Add(gid);
            }
        }

        return changed.ToImmutable();
    }

    private static IEnumerable<(string Gid, DigestionFormalizationSignature Signature)>
        CandidateSignatures(DigestionFormalizationReceipt candidate)
    {
        yield return (candidate.PrimaryGid, candidate.Signature);
        foreach (var extension in candidate.HostedExtensions.IsDefault
                     ? []
                     : candidate.HostedExtensions)
        {
            yield return (extension.Gid, extension.Signature);
        }
    }

    private static string? RequireCandidateReportSignature(
        string gidText,
        DigestionFormalizationSignature candidateSignature,
        LeanAxiomReport candidateReport)
    {
        if (!Gid.TryParse(gidText, out var gid))
        {
            return "candidate report signature clause requires a valid declaration GID: " + gidText;
        }

        try
        {
            var resolved = DigestionFormalizationReceipt.ResolveSignature(gid, candidateReport);
            return resolved == candidateSignature
                ? null
                : "candidate report signature clause requires the complete (name_key, kind, type) "
                    + "signature for "
                    + gidText;
        }
        catch (FormatException exception)
        {
            return "candidate report signature clause rejected " + gidText + ": " + exception.Message;
        }
    }

    private static Preliminary Reject(string clause) =>
        new(
            DigestionFormalizationReceiptTransitionResult.Rejected(clause),
            ImmutableHashSet<RepoPath>.Empty);
}

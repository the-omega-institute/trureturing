using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal sealed record DigestionGap(string Code, string Detail);

internal sealed record DigestionEntryEvaluation(
    DigestionLedgerEntry Entry,
    DigestionReceiptAlignment Alignment,
    DigestionStatus DerivedStatus,
    bool Deletable,
    ImmutableArray<DigestionGap> Gaps)
{
    internal string Render() =>
        $"{Entry.SourceId}/{Entry.AtomId} "
        + $"alignment={DigestionReceiptAlignmentNames.Render(Alignment)} "
        + $"{DigestionStatusNames.Migration(DerivedStatus.Migration)}-"
        + $"{DigestionStatusNames.Truth(DerivedStatus.Truth)} "
        + $"deletable={Deletable.ToString().ToLowerInvariant()} "
        + $"gaps={string.Join(',', Gaps.Select(static gap => gap.Code))}";
}

internal sealed record DigestionLedgerEvaluation(
    ImmutableArray<DigestionEntryEvaluation> Entries,
    ImmutableArray<string> Findings)
{
    internal int DeletableCount => Entries.Count(static entry => entry.Deletable);
}

internal static class DigestionStatusNames
{
    internal static string Migration(DigestionMigrationState value) => value switch
    {
        DigestionMigrationState.Residual => "residual",
        DigestionMigrationState.Partial => "partial",
        DigestionMigrationState.Absorbed => "absorbed",
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };

    internal static string Truth(DigestionTruthState value) => value switch
    {
        DigestionTruthState.Closed => "closed",
        DigestionTruthState.Tail => "tail",
        DigestionTruthState.Open => "open",
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
}

internal static class DigestionStatusEvaluator
{
    internal static DigestionLedgerEvaluation Evaluate(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        VerifiedScribeEmissions? verifiedScribeEmissions = null,
        BackfillInventoryDocument? baselineDocument = null,
        bool validateProjectedStatus = true)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        var entries = document.RequireDigestionEntries();
        var findings = ImmutableArray.CreateBuilder<string>();
        var duplicate = entries
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .FirstOrDefault(static group => group.Count() > 1);
        if (duplicate is not null)
        {
            findings.Add($"duplicate atom_id: {duplicate.Key}");
            return new DigestionLedgerEvaluation([], findings.ToImmutable());
        }

        var alignment = DigestionLedgerAligner.Evaluate(
            document,
            snapshot,
            baselineDocument,
            DigestionAlignmentMode.Admission);
        findings.AddRange(alignment.Findings);

        var dag = AcyclicTruthDag.Build(snapshot, lean) switch
        {
            DagBuildOutcome.Accepted accepted => accepted.Capability,
            DagBuildOutcome.Rejected rejected => throw new FormatException(
                "truth DAG is cyclic: " + string.Join(" -> ", rejected.Witness.Select(static path => path.Value))),
        };
        var nodes = dag.Nodes.ToDictionary(static node => node.RepoPath);
        var scribeAttestation = ScribeEmissionAttestation.Load(snapshot, findings);
        var work = entries.Select(entry =>
            Inspect(
                entry,
                alignment.AlignmentFor(entry.AtomId),
                snapshot,
                lean.Report,
                nodes,
                scribeAttestation,
                verifiedScribeEmissions,
                findings)).ToArray();
        DeriveMigration(work);

        var evaluations = ImmutableArray.CreateBuilder<DigestionEntryEvaluation>(work.Length);
        foreach (var item in work)
        {
            CompleteChainGaps(item, work);
            var truth = DeriveTruth(item, snapshot);
            var status = new DigestionStatus(item.Migration, truth);
            if (validateProjectedStatus && status != item.Entry.ProjectedStatus)
            {
                findings.Add(
                    $"entry {item.Entry.AtomId} handwritten status "
                    + $"{DigestionStatusNames.Migration(item.Entry.ProjectedStatus.Migration)}-"
                    + $"{DigestionStatusNames.Truth(item.Entry.ProjectedStatus.Truth)} differs from derived "
                    + $"{DigestionStatusNames.Migration(status.Migration)}-"
                    + DigestionStatusNames.Truth(status.Truth));
            }

            var gaps = item.Gaps
                .OrderBy(static gap => gap.Code, StringComparer.Ordinal)
                .ThenBy(static gap => gap.Detail, StringComparer.Ordinal)
                .ToImmutableArray();
            evaluations.Add(new DigestionEntryEvaluation(
                item.Entry,
                item.Alignment,
                status,
                item.Migration == DigestionMigrationState.Absorbed
                    && truth is DigestionTruthState.Closed or DigestionTruthState.Tail
                    && gaps.Length == 0,
                gaps));
        }

        return new DigestionLedgerEvaluation(
            evaluations.MoveToImmutable(),
            findings.Order(StringComparer.Ordinal).ToImmutableArray());
    }

    private static EntryWork Inspect(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        RepositorySnapshot snapshot,
        LeanAxiomReport leanReport,
        IReadOnlyDictionary<RepoPath, TruthNode> nodes,
        ScribeEmissionAttestation scribeAttestation,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        ImmutableArray<string>.Builder findings)
    {
        var gaps = new List<DigestionGap>();
        var boundary = entry.Atomizer == AtomizerRegistry.NoAtomizerId
            && entry.Boundary is not null
                ? VerifyBoundary(entry, snapshot, gaps, findings)
            : entry.CasRef is not null
            ? VerifyStructuredAlignment(entry, alignment, gaps, findings)
            : entry.Boundary is not null
                ? VerifyBoundary(entry, snapshot, gaps, findings)
                : VerifyStructuredAlignment(entry, alignment, gaps, findings);
        var targetStates = new List<(string Gid, TruthState State)>();
        var existingTargets = new Dictionary<string, RepositoryFile>(StringComparer.Ordinal);
        foreach (var gidText in entry.CoverageGids.Distinct(StringComparer.Ordinal))
        {
            if (!Gid.TryParse(gidText, out var gid)
                || !snapshot.TryGetFile(gid.Path.Value, out var target))
            {
                gaps.Add(new DigestionGap("target-gid-missing", gidText));
                continue;
            }

            if (!DeclarationExists(gid, leanReport, gaps))
            {
                continue;
            }

            existingTargets.Add(gidText, target);
            targetStates.Add((
                gidText,
                nodes.TryGetValue(target.Path, out var node) ? node.State : TruthState.Semantic));
        }

        if (entry.CoverageGids.Length == 0)
        {
            gaps.Add(new DigestionGap("coverage-gid-missing", entry.AtomId));
        }

        var coverage = VerifyCoverageReceipts(entry, existingTargets, gaps, findings);
        var scribe = VerifyScribeReceipts(
            entry,
            snapshot,
            scribeAttestation,
            verifiedScribeEmissions,
            gaps,
            findings);
        if (entry.Receipts.UnresolvedSubitems.Length > 0)
        {
            foreach (var subitem in entry.Receipts.UnresolvedSubitems)
            {
                gaps.Add(new DigestionGap("unresolved-subitem", subitem));
            }
        }

        var localComplete = boundary
            && existingTargets.Count == entry.CoverageGids.Distinct(StringComparer.Ordinal).Count()
            && entry.CoverageGids.Length > 0
            && coverage
            && scribe
            && entry.Receipts.UnresolvedSubitems.Length == 0;
        var hasProgress = existingTargets.Count > 0
            || entry.Receipts.Coverage.Length > 0
            || entry.Receipts.Scribe.Length > 0;
        return new EntryWork(entry, alignment, gaps, targetStates, localComplete, hasProgress);
    }

    private static bool DeclarationExists(
        Gid gid,
        LeanAxiomReport leanReport,
        ICollection<DigestionGap> gaps)
    {
        if (gid.ToTarget() is not Target.Formal { Declaration: { } declaration } formal)
        {
            return true;
        }

        if (!leanReport.Files.TryGetValue(formal.Path, out var module)
            || !string.IsNullOrEmpty(module.Error))
        {
            gaps.Add(new DigestionGap("target-declaration-missing", gid.Value));
            return false;
        }

        var suffix = "." + declaration;
        var matches = module.Declarations.Count(candidate =>
            string.Equals(candidate.Name, declaration, StringComparison.Ordinal)
            || candidate.Name.EndsWith(suffix, StringComparison.Ordinal));
        if (matches == 1)
        {
            return true;
        }

        gaps.Add(new DigestionGap(
            matches == 0 ? "target-declaration-missing" : "target-declaration-ambiguous",
            gid.Value));
        return false;
    }

    private static bool VerifyStructuredAlignment(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        if (!DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.RawSha256)
            || !DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.NormalizedSha256))
        {
            findings.Add($"entry {entry.AtomId} fingerprints must use canonical sha256:<64 lowercase hex>");
            gaps.Add(new DigestionGap("fingerprint-invalid", entry.AtomId));
            return false;
        }

        switch (alignment)
        {
            case DigestionReceiptAlignment.Seen:
                return true;
            case DigestionReceiptAlignment.NormalizedSeen:
                gaps.Add(new DigestionGap("normalized-seen-not-deletable", entry.AstPath));
                return false;
            case DigestionReceiptAlignment.Stale:
                gaps.Add(new DigestionGap("stale-receipt-not-deletable", entry.AstPath));
                return false;
            default:
                gaps.Add(new DigestionGap("structural-alignment-rejected", entry.AstPath));
                return false;
        }
    }

    private static bool VerifyBoundary(
        DigestionLedgerEntry entry,
        RepositorySnapshot snapshot,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        var boundary = entry.Boundary;
        if (boundary is null)
        {
            gaps.Add(new DigestionGap("boundary-not-reproducible", entry.AstPath));
            return false;
        }

        if (Path.GetFileName(entry.SourcePath).Contains(' ', StringComparison.Ordinal))
        {
            findings.Add($"source {entry.SourceId} filename contains spaces: {entry.SourcePath}");
        }

        if (!DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.RawSha256)
            || !DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.NormalizedSha256))
        {
            findings.Add($"entry {entry.AtomId} fingerprints must use canonical sha256:<64 lowercase hex>");
            gaps.Add(new DigestionGap("fingerprint-invalid", entry.AtomId));
            return false;
        }

        if (!snapshot.TryGetFile(entry.SourcePath, out var source))
        {
            gaps.Add(new DigestionGap("source-missing", entry.SourcePath));
            return false;
        }

        if (boundary.StartByte < 0
            || boundary.EndByte <= boundary.StartByte
            || boundary.EndByte > source.RawBytes.Length)
        {
            findings.Add(
                $"entry {entry.AtomId} byte span is outside {entry.SourcePath}; run make ingest");
            gaps.Add(new DigestionGap("boundary-span-invalid", boundary.AstPath));
            return false;
        }

        var storedSlice = source.RawBytes.AsSpan()[boundary.StartByte..boundary.EndByte];
        DigestionFingerprints fingerprints;
        try
        {
            fingerprints = DigestionFingerprint.Compute(storedSlice);
        }
        catch (DecoderFallbackException)
        {
            findings.Add(
                $"entry {entry.AtomId} boundary cuts invalid UTF-8 in {entry.SourcePath}; "
                + "run make ingest");
            gaps.Add(new DigestionGap("boundary-not-reproducible", boundary.AstPath));
            return false;
        }

        if (fingerprints != entry.Fingerprints)
        {
            findings.Add(
                $"entry {entry.AtomId} fingerprint disagrees with its source byte span; "
                + "run make ingest");
            gaps.Add(new DigestionGap("boundary-fingerprint-mismatch", boundary.AstPath));
            return false;
        }

        AtomizedTheoryDocument atomized;
        try
        {
            atomized = AtomizerRegistry.Atomize(entry.Atomizer, source.RawBytes.AsSpan());
        }
        catch (FormatException exception)
        {
            gaps.Add(new DigestionGap("boundary-not-reproducible", exception.Message));
            return false;
        }

        DigestionAtom atom;
        try
        {
            atom = atomized.ResolveClaim(boundary.AstPath);
        }
        catch (FormatException exception)
        {
            gaps.Add(new DigestionGap("boundary-not-reproducible", exception.Message));
            return false;
        }
        if (atom.StartByte != boundary.StartByte
            || atom.EndByte != boundary.EndByte
            || atom.Fingerprints != entry.Fingerprints)
        {
            gaps.Add(new DigestionGap("boundary-fingerprint-mismatch", boundary.AstPath));
            return false;
        }

        return true;
    }

    private static bool VerifyCoverageReceipts(
        DigestionLedgerEntry entry,
        IReadOnlyDictionary<string, RepositoryFile> targets,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        var receipts = UniqueByGid(entry.EntryLabel(), entry.Receipts.Coverage, static item => item.Gid, findings);
        var complete = true;
        foreach (var gid in entry.CoverageGids.Distinct(StringComparer.Ordinal))
        {
            if (!receipts.TryGetValue(gid, out var receipt))
            {
                gaps.Add(new DigestionGap("coverage-receipt-missing", gid));
                complete = false;
                continue;
            }

            if (!targets.TryGetValue(gid, out var target)
                || receipt.SourceSha256 != entry.Fingerprints.RawSha256
                || receipt.TargetSha256 != DigestionFingerprint.Compute(target.RawBytes.AsSpan()).RawSha256)
            {
                gaps.Add(new DigestionGap("coverage-receipt-mismatch", gid));
                complete = false;
            }
        }

        foreach (var extra in receipts.Keys.Except(entry.CoverageGids, StringComparer.Ordinal))
        {
            findings.Add($"entry {entry.AtomId} has an extra coverage receipt for {extra}");
            complete = false;
        }

        return complete;
    }

    private static bool VerifyScribeReceipts(
        DigestionLedgerEntry entry,
        RepositorySnapshot snapshot,
        ScribeEmissionAttestation attestation,
        VerifiedScribeEmissions? verifiedEmissions,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        var receipts = UniqueByGid(entry.EntryLabel(), entry.Receipts.Scribe, static item => item.Gid, findings);
        var complete = true;
        foreach (var gid in entry.CoverageGids.Distinct(StringComparer.Ordinal))
        {
            var hasReceipt = receipts.TryGetValue(gid, out var receipt);
            if (!hasReceipt)
            {
                gaps.Add(new DigestionGap("scribe-receipt-missing", gid));
                complete = false;
            }

            var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
            var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
            var emissionPath = ScribeEmissionAttestation.EmissionPath(documentGid);
            var selectsDeclaration = Gid.TryParse(gid, out var parsedGid)
                && parsedGid.ToTarget() is Target.Formal { Declaration: not null };
            var hasAttestation = attestation.TryGet(documentGid, out var emitted);
            if (!hasAttestation)
            {
                gaps.Add(new DigestionGap("scribe-attestation-missing", gid));
                complete = false;
            }

            ScribeEmissionRecord? verified = null;
            if (verifiedEmissions is not null
                && verifiedEmissions.TryGet(documentGid, out var verifiedRecord))
            {
                verified = verifiedRecord;
            }
            else
            {
                gaps.Add(new DigestionGap("scribe-emission-unverified", gid));
                complete = false;
            }

            if (selectsDeclaration
                && verifiedEmissions is not null
                && !verifiedEmissions.ReferencesDeclaration(gid))
            {
                gaps.Add(new DigestionGap("scribe-declaration-reference-missing", gid));
                complete = false;
            }

            if (!snapshot.TryGetFile(definitionPath, out var definition))
            {
                gaps.Add(new DigestionGap("scribe-definition-missing", gid));
                complete = false;
            }
            else if (hasReceipt
                && (receipt!.DefinitionSha256
                    != DigestionFingerprint.Compute(definition.RawBytes.AsSpan()).RawSha256
                    || hasAttestation
                    && (emitted!.DefinitionPath != definitionPath
                        || emitted.DefinitionSha256 != receipt.DefinitionSha256)
                    || verified is not null
                    && (verified.DefinitionPath != definitionPath
                        || verified.DefinitionSha256 != receipt.DefinitionSha256)))
            {
                gaps.Add(new DigestionGap("scribe-definition-mismatch", gid));
                complete = false;
            }

            if (!snapshot.TryGetFile(emissionPath, out var emission))
            {
                gaps.Add(new DigestionGap("scribe-emission-missing", gid));
                complete = false;
            }
            else if (hasReceipt
                && (receipt!.EmissionSha256
                    != DigestionFingerprint.Compute(emission.RawBytes.AsSpan()).RawSha256
                    || hasAttestation
                    && (emitted!.EmissionPath != emissionPath
                        || emitted.EmissionSha256 != receipt.EmissionSha256)
                    || verified is not null
                    && (verified.EmissionPath != emissionPath
                        || verified.EmissionSha256 != receipt.EmissionSha256)))
            {
                gaps.Add(new DigestionGap("scribe-emission-mismatch", gid));
                complete = false;
            }
        }

        foreach (var extra in receipts.Keys.Except(entry.CoverageGids, StringComparer.Ordinal))
        {
            findings.Add($"entry {entry.AtomId} has an extra Scribe receipt for {extra}");
            complete = false;
        }

        return complete;
    }

    private static Dictionary<string, T> UniqueByGid<T>(
        string label,
        IEnumerable<T> values,
        Func<T, string> gid,
        ImmutableArray<string>.Builder findings)
    {
        var result = new Dictionary<string, T>(StringComparer.Ordinal);
        foreach (var value in values)
        {
            var key = gid(value);
            if (!result.TryAdd(key, value))
            {
                findings.Add($"entry {label} has duplicate receipt for {key}");
            }
        }

        return result;
    }

    private static void DeriveMigration(IReadOnlyList<EntryWork> work)
    {
        foreach (var item in work)
        {
            item.Migration = item.LocalComplete && item.Entry.Receipts.ChainAtoms.Length == 0
                ? DigestionMigrationState.Absorbed
                : item.HasProgress
                    ? DigestionMigrationState.Partial
                    : DigestionMigrationState.Residual;
        }

        var byId = work.ToDictionary(static item => item.Entry.AtomId, StringComparer.Ordinal);
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var item in work.Where(static item =>
                         item.Migration != DigestionMigrationState.Absorbed && item.LocalComplete))
            {
                if (item.Entry.Receipts.ChainAtoms.All(atomId =>
                        byId.TryGetValue(atomId, out var dependency)
                        && dependency.Migration == DigestionMigrationState.Absorbed))
                {
                    item.Migration = DigestionMigrationState.Absorbed;
                    changed = true;
                }
            }
        }
    }

    private static void CompleteChainGaps(EntryWork item, IReadOnlyList<EntryWork> work)
    {
        var byId = work.ToDictionary(static candidate => candidate.Entry.AtomId, StringComparer.Ordinal);
        foreach (var atomId in item.Entry.Receipts.ChainAtoms)
        {
            if (!byId.TryGetValue(atomId, out var dependency)
                || dependency.Migration != DigestionMigrationState.Absorbed)
            {
                item.Gaps.Add(new DigestionGap("chain-migration-incomplete", atomId));
            }
        }
    }

    private static DigestionTruthState DeriveTruth(EntryWork item, RepositorySnapshot snapshot)
    {
        if (item.TargetStates.Count == 0
            || item.TargetStates.Any(static target => target.State is TruthState.Open or TruthState.Semantic))
        {
            foreach (var target in item.TargetStates.Where(static target =>
                         target.State is TruthState.Open or TruthState.Semantic))
            {
                item.Gaps.Add(new DigestionGap("lean-state-open", $"{target.Gid}:{target.State}"));
            }

            return DigestionTruthState.Open;
        }

        if (item.TargetStates.Any(static target => target.State == TruthState.Tail))
        {
            var tailGids = item.TargetStates
                .Where(static target => target.State == TruthState.Tail)
                .Select(static target => target.Gid)
                .ToArray();
            if (item.Migration != DigestionMigrationState.Absorbed
                || item.Entry.Receipts.TailAuthorization is null)
            {
                item.Gaps.Add(new DigestionGap(
                    "tail-authorization-missing",
                    string.Join(',', tailGids)));
                return DigestionTruthState.Open;
            }

            if (!TailAuthorizationArtifact.Verify(item.Entry, tailGids, snapshot))
            {
                item.Gaps.Add(new DigestionGap(
                    "tail-authorization-invalid",
                    string.Join(',', tailGids)));
                return DigestionTruthState.Open;
            }

            return DigestionTruthState.Tail;
        }

        return DigestionTruthState.Closed;
    }

    private static string EntryLabel(this DigestionLedgerEntry entry) => entry.AtomId;

    private sealed class EntryWork(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        List<DigestionGap> gaps,
        List<(string Gid, TruthState State)> targetStates,
        bool localComplete,
        bool hasProgress)
    {
        internal DigestionLedgerEntry Entry { get; } = entry;

        internal DigestionReceiptAlignment Alignment { get; } = alignment;

        internal List<DigestionGap> Gaps { get; } = gaps;

        internal List<(string Gid, TruthState State)> TargetStates { get; } = targetStates;

        internal bool LocalComplete { get; } = localComplete;

        internal bool HasProgress { get; } = hasProgress;

        internal DigestionMigrationState Migration { get; set; }
    }
}

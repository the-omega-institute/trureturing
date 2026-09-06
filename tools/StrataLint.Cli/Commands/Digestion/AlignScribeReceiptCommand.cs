using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class AlignScribeReceiptCommand
{
    private const string Usage = "USAGE: StrataLint align-scribe-receipt --seed-missing "
        + "(--atom ATOM_ID --gid GID | --pairs FILE) --base REV [--dry-run]";

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments) =>
        Run(repositoryRoot, repository, leanReportSource, scribeEmissionVerifier, arguments,
            static (root, path) => ImmutableArray.CreateRange(File.ReadAllBytes(Path.GetFullPath(path, root))),
            static (root, current, updates) => IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates));

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments,
        Func<string, string, ImmutableArray<byte>> readPairs,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> applyUpdates)
    {
        try
        {
            if (arguments.Contains("--seed-missing", StringComparer.Ordinal))
            {
                return Seed(repositoryRoot, repository, leanReportSource, scribeEmissionVerifier,
                    ParseSeedArguments(arguments, repositoryRoot, readPairs), applyUpdates);
            }

            return CoverAtomCommand.AlignScribeReceipt(repositoryRoot, repository, leanReportSource,
                scribeEmissionVerifier, arguments, applyUpdates);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"ALIGN_SCRIBE_RECEIPT_INVALID {exception.Message}\n");
        }
    }

    private static CommandResult Seed(
        string root,
        IRepositoryGateway repository,
        ILeanReportSource reportSource,
        IScribeEmissionVerifier verifier,
        SeedOptions options,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> applyUpdates)
    {
        var raw = repository.ReadCurrent();
        var current = Decode(raw);
        var baseline = Decode(repository.ReadRevision(options.BaseRevision));
        var document = BackfillInventoryLoader.Load(current);
        var baselineDocument = BackfillInventoryLoader.LoadBaseline(baseline);
        var report = reportSource.Load(current);
        var lean = LeanClosureValidator.Validate(current, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure => throw new InvalidOperationException(failure.Message),
        };
        var states = LeanTruthStates.Resolve(current, lean);
        var frozen = FrozenStatementIndex.Create(FrozenStateCatalog.Load(current), report);
        var verified = verifier.Verify(current, report);
        var entries = document.RequireDigestionEntries().ToLookup(static entry => entry.AtomId, StringComparer.Ordinal);
        var plans = options.Pairs.Select(pair => Inspect(pair, entries[pair.AtomId].ToArray(),
            current, report, states, frozen, verified)).ToArray();
        if (plans.Any(static plan => plan.Eligibility != SeedEligibility.Eligible))
        {
            var success = options.DryRun;
            return new CommandResult(success, Render(plans, options.DryRun, changed: false),
                success ? string.Empty : "ALIGN_SCRIBE_RECEIPT_INVALID "
                    + string.Join("; ", plans.Where(static plan => plan.Eligibility != SeedEligibility.Eligible)
                        .Select(static plan => $"{plan.Pair.AtomId}:{plan.Pair.Gid}:{Name(plan.Eligibility)}:{plan.Reason}")) + "\n");
        }

        var receipts = plans.ToLookup(static plan => plan.Pair.AtomId, StringComparer.Ordinal);
        var planned = Map(document, entry => receipts.Contains(entry.AtomId)
            ? entry with
            {
                Receipts = entry.Receipts with
                {
                    Scribe = entry.Receipts.Scribe.AddRange(receipts[entry.AtomId].Select(plan =>
                        DigestionReceiptBuilder.Build(ParseGid(plan.Pair.Gid), current, frozen, verified).Scribe)),
                },
            }
            : entry);
        var changes = RawChangeSet.Create(plans.Select(plan => EntryPath(plan.Entry!)).Distinct(StringComparer.Ordinal));
        var derived = Evaluate(planned, current, validateStatus: false);
        IngestCommand.RequireNoReceiptIntegrityFailure(derived);
        var statusChanges = derived.Entries
            .Where(static item => item.StatusAuthorityChanged && item.DerivedStatus != item.Entry.ProjectedStatus)
            .ToDictionary(static item => item.Entry.AtomId, StringComparer.Ordinal);
        planned = Map(planned, entry => statusChanges.TryGetValue(entry.AtomId, out var change)
            ? entry with { ProjectedStatus = change.DerivedStatus }
            : entry);
        var finalRaw = IngestCommand.ReplaceLedger(raw, document, planned);
        var final = Decode(finalRaw);
        LeanTruthStates.RequireSameManagedInputs(current, final);
        var evaluation = Evaluate(BackfillInventoryLoader.Load(final), final, validateStatus: true);
        IngestCommand.RequireNoReceiptIntegrityFailure(evaluation);
        var updates = IngestCommand.LedgerUpdates(raw, finalRaw);
        if (!options.DryRun)
            applyUpdates(root, raw, updates);
        var changed = !options.DryRun && updates.Length > 0;
        return new CommandResult(true, Render(plans, options.DryRun, changed)
            + RenderStatusChanges(statusChanges.Values, options.DryRun, changed), string.Empty);

        DigestionLedgerEvaluation Evaluate(BackfillInventoryDocument candidate, RepositorySnapshot snapshot, bool validateStatus) =>
            DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.ChangedSet, candidate, snapshot, lean,
                verified, baselineDocument, validateProjectedStatus: validateStatus, baselineSnapshot: baseline,
                changes: changes, truthStates: states);
    }

    private static SeedPlan Inspect(
        SeedPair pair,
        DigestionLedgerEntry[] entries,
        RepositorySnapshot current,
        LeanAxiomReport report,
        IReadOnlyDictionary<RepoPath, TruthState> states,
        FrozenStatementIndex frozen,
        VerifiedScribeEmissions verified)
    {
        if (entries.Length != 1)
            return new SeedPlan(pair, null, SeedEligibility.AmbiguousEdge, "SEED_ATOM_AMBIGUOUS");
        var entry = entries[0];
        var edges = entry.Coverage.Where(edge => edge.Gid == pair.Gid).ToArray();
        if (edges.Length != 1)
            return new SeedPlan(pair, entry, SeedEligibility.AmbiguousEdge, "SEED_EDGE_AMBIGUOUS");
        if (entry.Receipts.Scribe.Count(receipt => receipt.Gid == pair.Gid) != 0)
            return new SeedPlan(pair, entry, SeedEligibility.AmbiguousEdge, "SEED_RECEIPT_PRESENT");

        var edge = CurrentEdgeValidator.Validate(pair.Gid, current, report, states, frozen);
        if (!edge.IsClosed)
            return new SeedPlan(pair, entry, SeedEligibility.AmbiguousEdge, "SEED_EDGE_NOT_CLOSED: " + edge.Diagnostic);
        if (edges[0].TargetStatementId != edge.TargetStatementId)
            return new SeedPlan(pair, entry, SeedEligibility.AmbiguousEdge, "SEED_TARGET_MISMATCH");
        var documentGid = ScribeEmissionAttestation.DocumentGid(pair.Gid);
        if (!current.TryGetFile(ScribeEmissionAttestation.DefinitionPath(documentGid), out _))
            return new SeedPlan(pair, entry, SeedEligibility.MissingDefinition, "SEED_DEFINITION_ABSENT");
        if (!verified.TryGet(documentGid, out _))
            return new SeedPlan(pair, entry, SeedEligibility.MissingEmission, "SEED_EMISSION_UNVERIFIED");
        if (ParseGid(pair.Gid).ToTarget() is Target.Formal { Declaration: not null }
            && !verified.ReferencesDeclaration(pair.Gid))
            return new SeedPlan(pair, entry, SeedEligibility.MissingDeclarationReference, "SEED_DECLARATION_REFERENCE_ABSENT");
        return new SeedPlan(pair, entry, SeedEligibility.Eligible, string.Empty);
    }

    private static SeedOptions ParseSeedArguments(
        IReadOnlyList<string> arguments,
        string root,
        Func<string, string, ImmutableArray<byte>> readPairs)
    {
        string? atom = null, gid = null, path = null, baseline = null;
        var seed = false;
        var dryRun = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--seed-missing" when !seed: seed = true; break;
                case "--dry-run" when !dryRun: dryRun = true; break;
                case "--atom" when atom is null: atom = Value(); break;
                case "--gid" when gid is null: gid = Value(); break;
                case "--pairs" when path is null: path = Value(); break;
                case "--base" when baseline is null: baseline = Value(); break;
                default: throw new InvalidOperationException(Usage);
            }

            string Value()
            {
                if (++index >= arguments.Count || string.IsNullOrWhiteSpace(arguments[index])
                    || arguments[index] != arguments[index].Trim() || arguments[index].StartsWith("--", StringComparison.Ordinal))
                    throw new InvalidOperationException(Usage);
                return arguments[index];
            }
        }

        if (!seed || baseline is null || (path is null ? atom is null || gid is null : atom is not null || gid is not null))
            throw new InvalidOperationException(Usage);
        var pairs = path is null ? ImmutableArray.Create(new SeedPair(atom!, gid!)) : ReadPairs(readPairs(root, path));
        if (pairs.IsEmpty || pairs.Distinct().Count() != pairs.Length
            || pairs.Any(pair => !DigestionFingerprint.IsCanonicalSha256("sha256:" + pair.AtomId)
                || !Gid.TryParse(pair.Gid, out var parsed) || parsed.ToTarget() is not Target.Formal))
            throw new InvalidOperationException("SEED_PAIRS_INVALID " + Usage);
        return new SeedOptions(pairs, baseline, dryRun);
    }

    private static ImmutableArray<SeedPair> ReadPairs(ImmutableArray<byte> bytes)
    {
        if (bytes.IsEmpty || bytes[^1] != (byte)'\n' || bytes.AsSpan().Contains((byte)'\r')
            || bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
            throw new InvalidOperationException("SEED_PAIRS_INVALID expected UTF-8 TSV without BOM/CR, ending in LF");
        string text;
        try { text = new UTF8Encoding(false, true).GetString(bytes.AsSpan()); }
        catch (DecoderFallbackException exception) { throw new InvalidOperationException("SEED_PAIRS_INVALID UTF-8", exception); }
        var pairs = ImmutableArray.CreateBuilder<SeedPair>();
        using var reader = new StringReader(text);
        while (reader.ReadLine() is { } line)
        {
            var fields = line.Split('\t');
            if (fields.Length != 2 || fields.Any(field => string.IsNullOrWhiteSpace(field) || field != field.Trim()))
                throw new InvalidOperationException("SEED_PAIRS_INVALID expected ATOM_ID<TAB>GID");
            pairs.Add(new SeedPair(fields[0], fields[1]));
        }
        return pairs.ToImmutable();
    }

    private static BackfillInventoryDocument Map(BackfillInventoryDocument document,
        Func<DigestionLedgerEntry, DigestionLedgerEntry> transform) =>
        document.WithDigestionSources(document.RequireDigestionSources().Select(source => source with
        { Entries = source.Entries.Select(transform).ToImmutableArray() }).ToImmutableArray());

    private static Gid ParseGid(string text) => Gid.TryParse(text, out var gid)
        ? gid : throw new InvalidOperationException("SEED_PAIRS_INVALID GID: " + text);

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(failure.Message),
    };

    private static string EntryPath(DigestionLedgerEntry entry) => BackfillInventoryLoader.RootPath
        + entry.SourceId + "/" + DigestionStatusNames.Migration(entry.ProjectedStatus.Migration) + "-"
        + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth) + "/" + entry.AtomId + ".yaml";

    private static string Render(IEnumerable<SeedPlan> plans, bool dryRun, bool changed) =>
        string.Concat(plans.Select(plan => $"SCRIBE_SEED atom_id={plan.Pair.AtomId} gid={plan.Pair.Gid} "
            + $"eligibility={Name(plan.Eligibility)} reason={plan.Reason} "
            + $"dry_run={dryRun.ToString().ToLowerInvariant()} ledger_changed={changed.ToString().ToLowerInvariant()}\n"));

    private static string RenderStatusChanges(IEnumerable<DigestionEntryEvaluation> changes, bool dryRun, bool changed) =>
        string.Concat(changes.OrderBy(static item => item.Entry.AtomId, StringComparer.Ordinal).Select(item =>
            $"SCRIBE_SEED_STATUS atom_id={item.Entry.AtomId} "
            + $"from={DigestionStatusNames.Migration(item.Entry.ProjectedStatus.Migration)}-"
            + $"{DigestionStatusNames.Truth(item.Entry.ProjectedStatus.Truth)} "
            + $"to={DigestionStatusNames.Migration(item.DerivedStatus.Migration)}-"
            + $"{DigestionStatusNames.Truth(item.DerivedStatus.Truth)} "
            + $"dry_run={dryRun.ToString().ToLowerInvariant()} ledger_changed={changed.ToString().ToLowerInvariant()}\n"));

    private static string Name(SeedEligibility eligibility) => eligibility switch
    {
        SeedEligibility.Eligible => "eligible",
        SeedEligibility.MissingDefinition => "missing-definition",
        SeedEligibility.MissingEmission => "missing-emission",
        SeedEligibility.MissingDeclarationReference => "missing-declaration-reference",
        SeedEligibility.AmbiguousEdge => "ambiguous-edge",
        _ => throw new ArgumentOutOfRangeException(nameof(eligibility)),
    };

    private enum SeedEligibility { Eligible, MissingDefinition, MissingEmission, MissingDeclarationReference, AmbiguousEdge }
    private sealed record SeedPair(string AtomId, string Gid);
    private sealed record SeedOptions(ImmutableArray<SeedPair> Pairs, string BaseRevision, bool DryRun);
    private sealed record SeedPlan(SeedPair Pair, DigestionLedgerEntry? Entry, SeedEligibility Eligibility, string Reason);
}

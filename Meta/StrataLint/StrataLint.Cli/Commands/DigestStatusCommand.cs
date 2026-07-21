using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestStatusCommand
{
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
    };

    internal static CommandResult Run(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var options = ParseArguments(arguments);
            var snapshot = Decode(repository.ReadCurrent());
            if (!snapshot.TryGetFile(BackfillInventoryLoader.RelativePath, out var ledgerFile))
            {
                throw new InvalidOperationException($"{BackfillInventoryLoader.RelativePath} is missing");
            }

            var leanReport = leanReportSource.Load(snapshot);
            var lean = ValidateLean(snapshot, leanReport);
            var verifiedScribeEmissions = scribeEmissionVerifier.Verify(leanReport);
            var document = BackfillInventoryLoader.Load(ledgerFile.Text);
            RepositorySnapshot? baselineSnapshot = null;
            BackfillInventoryDocument? baselineDocument = null;
            if (options.BaselineRevision is not null)
            {
                baselineSnapshot = Decode(repository.ReadRevision(options.BaselineRevision));
                if (!baselineSnapshot.TryGetFile(BackfillInventoryLoader.RelativePath, out var baselineLedger))
                {
                    throw new InvalidOperationException(
                        $"baseline {BackfillInventoryLoader.RelativePath} is missing");
                }

                baselineDocument = BackfillInventoryLoader.Load(baselineLedger.Text);
            }

            var evaluation = DigestionStatusEvaluator.Evaluate(
                document,
                snapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument);
            if (evaluation.Findings.Length > 0)
            {
                var error = "DIGEST_STATUS_INVALID count=" + evaluation.Findings.Length + "\n"
                    + string.Concat(evaluation.Findings.Select(static finding => $"FINDING {finding}\n"));
                return new CommandResult(false, string.Empty, error);
            }

            if (!options.ResidualSummary)
            {
                return new CommandResult(
                    true,
                    options.Json ? RenderJson(evaluation) : RenderText(evaluation),
                    string.Empty);
            }

            var candidateSnapshotSha256 = CanonicalSnapshotSha256(snapshot);
            var baselineSnapshotSha256 = CanonicalSnapshotSha256(
                baselineSnapshot ?? throw new InvalidOperationException("residual summary requires --base REV"));
            var residualBlock = DigestResidualSummary.Render(
                evaluation,
                candidateSnapshotSha256,
                baselineSnapshotSha256);
            if (options.VerifyReviewPath is null)
            {
                return new CommandResult(true, residualBlock, string.Empty);
            }

            var reviewBytes = File.ReadAllBytes(options.VerifyReviewPath);
            return DigestResidualSummary.ContainsExactlyOneVerbatimBlock(reviewBytes, residualBlock)
                ? new CommandResult(
                    true,
                    $"ECHO_REVIEW_VALID candidate_snapshot_sha256={candidateSnapshotSha256} "
                        + $"baseline_snapshot_sha256={baselineSnapshotSha256}\n",
                    string.Empty)
                : new CommandResult(
                    false,
                    string.Empty,
                    "ECHO_REVIEW_INVALID residual summary block is missing, duplicated, stale, reordered, or modified\n");
        }
        catch (Exception exception) when (
            exception is FormatException
                or InvalidOperationException
                or IOException
                or ArgumentException)
        {
            return new CommandResult(false, string.Empty, $"DIGEST_STATUS_INVALID {exception.Message}\n");
        }
    }

    private static DigestStatusOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        var json = false;
        var residualSummary = false;
        string? baselineRevision = null;
        string? verifyReviewPath = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--json" when !json:
                    json = true;
                    break;
                case "--residual-summary" when !residualSummary:
                    residualSummary = true;
                    break;
                case "--base" when baselineRevision is null && index + 1 < arguments.Count:
                    baselineRevision = arguments[++index];
                    if (string.IsNullOrWhiteSpace(baselineRevision)) throw Usage();
                    break;
                case "--verify-review" when verifyReviewPath is null && index + 1 < arguments.Count:
                    verifyReviewPath = arguments[++index];
                    if (string.IsNullOrWhiteSpace(verifyReviewPath)) throw Usage();
                    break;
                default:
                    throw Usage();
            }
        }

        if (json && residualSummary
            || residualSummary && baselineRevision is null
            || verifyReviewPath is not null && !residualSummary)
        {
            throw Usage();
        }

        return new DigestStatusOptions(json, residualSummary, baselineRevision, verifyReviewPath);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint digest-status [--json] [--base REV] | "
            + "--residual-summary --base REV [--verify-review FILE]");

    private static string CanonicalSnapshotSha256(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile("Meta/registry.yaml", out var registry)
            || !snapshot.TryGetFile("Meta/domains.yaml", out var domains))
        {
            throw new InvalidOperationException("snapshot policy inputs are missing");
        }

        var registryOutcome = RegistryLoader.Load(registry.RawBytes.AsSpan(), domains.RawBytes.AsSpan());
        var policy = registryOutcome is RegistryLoadOutcome.Accepted accepted
            ? accepted.Policy
            : throw new InvalidOperationException(
                ((RegistryLoadOutcome.InfrastructureFailure)registryOutcome).Message);
        var canonicalization = RepositoryCanonicalizer.Validate(snapshot, policy);
        return canonicalization is CanonicalizationOutcome.Accepted canonical
            ? "sha256:" + canonical.Capability.Sha256
            : throw new InvalidOperationException(
                ((CanonicalizationOutcome.InfrastructureFailure)canonicalization).Message);
    }

    internal static string RenderText(DigestionLedgerEvaluation evaluation)
    {
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine(
            $"DIGEST_STATUS entries={evaluation.Entries.Length} deletable_now={evaluation.DeletableCount}");
        foreach (var entry in evaluation.Entries
                     .OrderBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                     .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal))
        {
            writer.WriteLine("ENTRY " + entry.Render());
            foreach (var gap in entry.Gaps)
            {
                writer.WriteLine(
                    $"GAP atom={entry.Entry.AtomId} code={gap.Code} detail={JsonSerializer.Serialize(gap.Detail)}");
            }
        }

        return writer.ToString();
    }

    private static string RenderJson(DigestionLedgerEvaluation evaluation)
    {
        var material = new
        {
            schema = "stratalint-digest-status-v1",
            entries_total = evaluation.Entries.Length,
            deletable_now = evaluation.DeletableCount,
            entries = evaluation.Entries
                .OrderBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal)
                .Select(static item => new
                {
                    source_id = item.Entry.SourceId,
                    atom_id = item.Entry.AtomId,
                    ast_path = item.Entry.AstPath,
                    alignment = DigestionReceiptAlignmentNames.Render(item.Alignment),
                    migration = DigestionStatusNames.Migration(item.DerivedStatus.Migration),
                    truth = DigestionStatusNames.Truth(item.DerivedStatus.Truth),
                    deletable = item.Deletable,
                    gaps = item.Gaps.Select(static gap => new
                    {
                        code = gap.Code,
                        detail = gap.Detail,
                    }),
                }),
        };
        return JsonSerializer.Serialize(material, JsonOptions) + "\n";
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private sealed record DigestStatusOptions(
        bool Json,
        bool ResidualSummary,
        string? BaselineRevision,
        string? VerifyReviewPath);
}

internal static class DigestResidualSummary
{
    internal const string StartMarker = "<!-- stratalint:echo-residual-summary:start -->";
    internal const string EndMarker = "<!-- stratalint:echo-residual-summary:end -->";
    private const string ResidualGapCode = "unresolved-subitem";

    internal static string Render(
        DigestionLedgerEvaluation evaluation,
        string candidateSnapshotSha256,
        string baselineSnapshotSha256)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        ArgumentException.ThrowIfNullOrWhiteSpace(candidateSnapshotSha256);
        ArgumentException.ThrowIfNullOrWhiteSpace(baselineSnapshotSha256);
        var sources = evaluation.Entries
            .GroupBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
            .OrderBy(static group => group.Key, StringComparer.Ordinal)
            .Select(static group => new SourceResiduals(
                group.Key,
                group
                    .Select(static item => new AtomResiduals(
                        item.Entry.AtomId,
                        item.Gaps
                            .Where(static gap => gap.Code == ResidualGapCode)
                            .Select(static gap => gap.Detail)
                            .OrderBy(static detail => detail, StringComparer.Ordinal)
                            .ToArray()))
                    .Where(static item => item.Subitems.Length > 0)
                    .OrderBy(static item => item.AtomId, StringComparer.Ordinal)
                    .ToArray()))
            .ToArray();
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine(StartMarker);
        writer.WriteLine("# Echo Residual Summary");
        writer.WriteLine();
        writer.WriteLine($"- candidate_snapshot_sha256: `{candidateSnapshotSha256}`");
        writer.WriteLine($"- baseline_snapshot_sha256: `{baselineSnapshotSha256}`");
        writer.WriteLine($"- unresolved_subitems: {sources.Sum(static source => source.SubitemCount)}");
        writer.WriteLine($"- mother_residual_atom_ids: {sources.Sum(static source => source.Atoms.Length)}");

        foreach (var source in sources)
        {
            writer.WriteLine();
            writer.WriteLine($"## `{source.SourceId}`");
            writer.WriteLine();
            writer.WriteLine($"- unresolved_subitems: {source.SubitemCount}");
            writer.WriteLine($"- mother_residual_atom_ids: {source.Atoms.Length}");
            writer.WriteLine();
            if (source.Atoms.Length == 0)
            {
                writer.WriteLine("Mother residual atoms: none.");
                continue;
            }

            writer.WriteLine("Mother residual atoms:");
            writer.WriteLine();
            foreach (var atom in source.Atoms)
            {
                writer.WriteLine($"- `{atom.AtomId}` ({atom.Subitems.Length})");
                foreach (var subitem in atom.Subitems)
                {
                    writer.WriteLine($"  - `{subitem}`");
                }
            }
        }

        writer.WriteLine();
        writer.WriteLine(EndMarker);

        return writer.ToString();
    }

    internal static bool ContainsExactlyOneVerbatimBlock(
        ReadOnlySpan<byte> reviewBytes,
        string expectedBlock)
    {
        ArgumentNullException.ThrowIfNull(expectedBlock);
        var startMarker = Encoding.UTF8.GetBytes(StartMarker);
        var endMarker = Encoding.UTF8.GetBytes(EndMarker);
        if (CountOccurrences(reviewBytes, startMarker) != 1
            || CountOccurrences(reviewBytes, endMarker) != 1)
        {
            return false;
        }

        var expectedBytes = Encoding.UTF8.GetBytes(expectedBlock);
        var start = reviewBytes.IndexOf(startMarker);
        return start >= 0
            && reviewBytes.Length - start >= expectedBytes.Length
            && reviewBytes.Slice(start, expectedBytes.Length).SequenceEqual(expectedBytes);
    }

    private static int CountOccurrences(ReadOnlySpan<byte> input, ReadOnlySpan<byte> value)
    {
        var count = 0;
        while (input.IndexOf(value) is var index && index >= 0)
        {
            count++;
            input = input[(index + value.Length)..];
        }

        return count;
    }

    private sealed record AtomResiduals(string AtomId, string[] Subitems);

    private sealed record SourceResiduals(string SourceId, AtomResiduals[] Atoms)
    {
        internal int SubitemCount => Atoms.Sum(static atom => atom.Subitems.Length);
    }
}

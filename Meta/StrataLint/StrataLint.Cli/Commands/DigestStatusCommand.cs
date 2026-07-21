using System.Text.Json;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestStatusCommand
{
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
    };
    private static readonly byte[] NulSeparator = [0];
    private static readonly byte[] LineSeparator = [(byte)'\n'];

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
            var material = Evaluate(
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                options.BaselineRevision);
            if (material.Evaluation.Findings.Length > 0)
            {
                var error = "DIGEST_STATUS_INVALID count=" + material.Evaluation.Findings.Length + "\n"
                    + string.Concat(material.Evaluation.Findings.Select(static finding => $"FINDING {finding}\n"));
                return new CommandResult(false, string.Empty, error);
            }

            return new CommandResult(
                true,
                options.ResidualSummary
                    ? DigestResidualSummary.Render(material.Evaluation, material.Binding)
                    : options.Json
                        ? RenderJson(material.Evaluation)
                        : RenderText(material.Evaluation),
                string.Empty);
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
                default:
                    throw Usage();
            }
        }

        if (json && residualSummary) throw Usage();
        return new DigestStatusOptions(json, residualSummary, baselineRevision);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint digest-status [--json|--residual-summary] [--base REV]");

    internal static DigestStatusMaterial Evaluate(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        string? baselineRevision)
    {
        var rawSnapshot = repository.ReadCurrent();
        var snapshot = Decode(rawSnapshot);
        if (!snapshot.TryGetFile(BackfillInventoryLoader.RelativePath, out var ledgerFile))
        {
            throw new InvalidOperationException($"{BackfillInventoryLoader.RelativePath} is missing");
        }

        var leanReport = leanReportSource.Load(snapshot);
        var lean = ValidateLean(snapshot, leanReport);
        var verifiedScribeEmissions = scribeEmissionVerifier.Verify(leanReport);
        var document = BackfillInventoryLoader.Load(ledgerFile.Text);
        BackfillInventoryDocument? baselineDocument = null;
        string? baselineSnapshotSha256 = null;
        if (baselineRevision is not null)
        {
            var rawBaseline = repository.ReadRevision(baselineRevision);
            var baseline = Decode(rawBaseline);
            if (!baseline.TryGetFile(BackfillInventoryLoader.RelativePath, out var baselineLedger))
            {
                throw new InvalidOperationException(
                    $"baseline {BackfillInventoryLoader.RelativePath} is missing");
            }

            baselineDocument = BackfillInventoryLoader.Load(baselineLedger.Text);
            baselineSnapshotSha256 = SnapshotSha256(rawBaseline);
        }

        var evaluation = DigestionStatusEvaluator.Evaluate(
            document,
            snapshot,
            lean,
            verifiedScribeEmissions,
            baselineDocument);
        return new DigestStatusMaterial(
            evaluation,
            new EchoReviewSnapshotBinding(
                SnapshotSha256(rawSnapshot),
                baselineRevision,
                baselineSnapshotSha256));
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
        string? BaselineRevision);

    private static string SnapshotSha256(RawRepositorySnapshot snapshot)
    {
        using var sha256 = SHA256.Create();
        foreach (var entry in snapshot.Entries.OrderBy(static entry => entry.Path, StringComparer.Ordinal))
        {
            UpdateUtf8(sha256, entry.Path);
            sha256.TransformBlock(NulSeparator, 0, NulSeparator.Length, null, 0);
            UpdateUtf8(sha256, entry.Bytes.Length.ToString(System.Globalization.CultureInfo.InvariantCulture));
            sha256.TransformBlock(NulSeparator, 0, NulSeparator.Length, null, 0);
            var bytes = entry.Bytes.ToArray();
            sha256.TransformBlock(bytes, 0, bytes.Length, null, 0);
            sha256.TransformBlock(LineSeparator, 0, LineSeparator.Length, null, 0);
        }

        sha256.TransformFinalBlock(Array.Empty<byte>(), 0, 0);
        return "sha256:" + Convert.ToHexString(sha256.Hash!).ToLowerInvariant();
    }

    private static void UpdateUtf8(HashAlgorithm algorithm, string value)
    {
        var bytes = Encoding.UTF8.GetBytes(value);
        algorithm.TransformBlock(bytes, 0, bytes.Length, null, 0);
    }
}

internal sealed record DigestStatusMaterial(
    DigestionLedgerEvaluation Evaluation,
    EchoReviewSnapshotBinding Binding);

internal sealed record EchoReviewSnapshotBinding(
    string CandidateSnapshotSha256,
    string? BaselineRevision,
    string? BaselineSnapshotSha256);

internal static class DigestResidualSummary
{
    private const string ResidualGapCode = "unresolved-subitem";

    internal static string Render(
        DigestionLedgerEvaluation evaluation,
        EchoReviewSnapshotBinding? binding = null)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
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
        writer.WriteLine("# Echo Residual Summary");
        writer.WriteLine();
        if (binding is not null)
        {
            writer.WriteLine($"- candidate_snapshot_sha256: {binding.CandidateSnapshotSha256}");
            writer.WriteLine($"- base_revision: {binding.BaselineRevision ?? "none"}");
            writer.WriteLine($"- baseline_snapshot_sha256: {binding.BaselineSnapshotSha256 ?? "none"}");
            writer.WriteLine();
        }

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

        return writer.ToString();
    }

    private sealed record AtomResiduals(string AtomId, string[] Subitems);

    private sealed record SourceResiduals(string SourceId, AtomResiduals[] Atoms)
    {
        internal int SubitemCount => Atoms.Sum(static atom => atom.Subitems.Length);
    }
}

internal static class EchoReviewVerifyCommand
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        try
        {
            var options = ParseArguments(arguments);
            var material = DigestStatusCommand.Evaluate(
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                options.BaselineRevision);
            if (material.Evaluation.Findings.Length > 0)
            {
                var error = "ECHO_REVIEW_INVALID count=" + material.Evaluation.Findings.Length + "\n"
                    + string.Concat(material.Evaluation.Findings.Select(static finding => $"FINDING {finding}\n"));
                return new CommandResult(false, string.Empty, error);
            }

            var expected = StrictUtf8.GetBytes(DigestResidualSummary.Render(material.Evaluation, material.Binding));
            var path = ResolveReviewPath(repositoryRoot, options.Path);
            if (!File.Exists(path.FullPath))
            {
                return new CommandResult(
                    false,
                    string.Empty,
                    $"ECHO_REVIEW_INVALID missing path={path.RelativePath}; run make echo-residual-summary BASE={options.BaselineRevision ?? "origin/dev"} > {path.RelativePath}\n");
            }

            var actual = File.ReadAllBytes(path.FullPath);
            if (!actual.AsSpan().SequenceEqual(expected))
            {
                return new CommandResult(
                    false,
                    string.Empty,
                    $"ECHO_REVIEW_INVALID mismatch path={path.RelativePath} expected_bytes={expected.Length} actual_bytes={actual.Length} first_difference={FirstDifference(expected, actual)}\n");
            }

            return new CommandResult(
                true,
                $"ECHO_REVIEW_VERIFIED path={path.RelativePath} bytes={actual.Length} base={options.BaselineRevision ?? "none"}\n",
                string.Empty);
        }
        catch (Exception exception) when (
            exception is FormatException
                or InvalidOperationException
                or IOException
                or ArgumentException
                or UnauthorizedAccessException)
        {
            return new CommandResult(false, string.Empty, $"ECHO_REVIEW_INVALID {exception.Message}\n");
        }
    }

    private static EchoReviewVerifyOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        string? baselineRevision = null;
        string path = ".echo-review.md";
        var pathSet = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--base" when baselineRevision is null && index + 1 < arguments.Count:
                    baselineRevision = arguments[++index];
                    if (string.IsNullOrWhiteSpace(baselineRevision)) throw Usage();
                    break;
                default:
                    if (pathSet) throw Usage();
                    path = arguments[index];
                    if (string.IsNullOrWhiteSpace(path)) throw Usage();
                    pathSet = true;
                    break;
            }
        }

        return new EchoReviewVerifyOptions(baselineRevision, path);
    }

    private static ReviewPath ResolveReviewPath(string repositoryRoot, string path)
    {
        var root = Path.GetFullPath(repositoryRoot);
        var fullPath = Path.GetFullPath(Path.IsPathRooted(path) ? path : Path.Combine(root, path));
        if (!fullPath.Equals(root, StringComparison.Ordinal)
            && !fullPath.StartsWith(root + Path.DirectorySeparatorChar, StringComparison.Ordinal))
        {
            throw new InvalidOperationException("echo review path must stay inside the repository");
        }

        var relative = Path.GetRelativePath(root, fullPath).Replace(Path.DirectorySeparatorChar, '/');
        return new ReviewPath(fullPath, relative);
    }

    private static int FirstDifference(byte[] expected, byte[] actual)
    {
        var length = Math.Min(expected.Length, actual.Length);
        for (var index = 0; index < length; index++)
        {
            if (expected[index] != actual[index]) return index;
        }

        return length;
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint echo-review-verify [--base REV] [PATH]");

    private sealed record EchoReviewVerifyOptions(string? BaselineRevision, string Path);

    private sealed record ReviewPath(string FullPath, string RelativePath);
}

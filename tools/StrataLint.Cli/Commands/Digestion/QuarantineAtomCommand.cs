using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Cli;

internal static class QuarantineAtomCommand
{
    private const string Usage =
        "USAGE: StrataLint quarantine-atom --request FILE --base REV [--replace] | "
        + "quarantine-atom --clear ATOM_ID --base REV";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly ImmutableHashSet<string> RequestKeys =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "atom_id",
            "blocker_class",
            "justification",
            "reentry_condition");

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments) =>
        Run(repositoryRoot, repository, arguments, BackfillInventoryWriter.WriteAtom);

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments,
        Func<DigestionLedgerEntry, ImmutableArray<byte>> writeAtom)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(writeAtom);
        try
        {
            var options = ParseArguments(arguments);
            var request = options.RequestPath is null
                ? null
                : LoadRequest(repositoryRoot, options.RequestPath);
            var atomId = request?.AtomId ?? options.ClearAtomId!;
            var currentRaw = repository.ReadCurrent();
            _ = repository.ReadRevision(options.BaseRevision);
            var current = Decode(currentRaw);
            var document = BackfillInventoryLoader.Load(current);
            var target = LocateTarget(document, atomId);
            RequireWritable(target);
            var path = LocateShard(currentRaw, target);

            if (request is null)
            {
                if (target.Receipts.Quarantine is null)
                {
                    throw Invalid("QUARANTINE_ABSENT", $"atom_id={atomId}");
                }

                var cleared = target with
                {
                    Receipts = target.Receipts with { Quarantine = null },
                };
                Write(repositoryRoot, currentRaw, path, cleared, writeAtom);
                return Success($"QUARANTINE_CLEARED atom_id={atomId} path={path}");
            }

            var planned = new DigestionQuarantine(
                request.Justification,
                request.ReentryCondition,
                request.BlockerClass);
            if (target.Receipts.Quarantine == planned)
            {
                return Success(
                    $"QUARANTINE_WRITTEN atom_id={atomId} "
                    + $"blocker_class={request.BlockerClass} path={path}");
            }

            var replacing = target.Receipts.Quarantine is not null;
            if (replacing && !options.Replace)
            {
                throw Invalid("QUARANTINE_CONFLICT", $"atom_id={atomId}");
            }

            var updated = target with
            {
                Receipts = target.Receipts with { Quarantine = planned },
            };
            Write(repositoryRoot, currentRaw, path, updated, writeAtom);
            var sentinel = replacing
                ? "QUARANTINE_REPLACED"
                : "QUARANTINE_WRITTEN";
            return Success(
                $"{sentinel} atom_id={atomId} blocker_class={request.BlockerClass} path={path}");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"QUARANTINE_INVALID {exception.Message}\n");
        }
    }

    private static void Write(
        string repositoryRoot,
        RawRepositorySnapshot current,
        string path,
        DigestionLedgerEntry updated,
        Func<DigestionLedgerEntry, ImmutableArray<byte>> writeAtom)
    {
        ImmutableArray<byte> bytes;
        try
        {
            bytes = writeAtom(updated);
            var overlaid = RawRepositorySnapshot.Create(current.Entries.Select(entry =>
                string.Equals(entry.Path, path, StringComparison.Ordinal)
                    ? new RawRepositoryEntry(entry.Path, bytes, entry.GitBlobOid)
                    : entry));
            var replayed = BackfillInventoryLoader.Load(Decode(overlaid));
            var replayedEntry = LocateTarget(replayed, updated.AtomId);
            if (replayedEntry != updated
                || !writeAtom(replayedEntry).AsSpan().SequenceEqual(bytes.AsSpan()))
            {
                throw new FormatException("serialized shard did not replay byte-identically");
            }
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            throw Invalid("ROUND_TRIP_FAILED", exception.Message);
        }

        IngestCommand.ApplyLedgerUpdatesAtomically(
            repositoryRoot,
            current,
            [new IngestCommand.LedgerUpdate(path, bytes)]);
    }

    private static QuarantineRequest LoadRequest(string repositoryRoot, string requestedPath)
    {
        var path = ResolveRequestPath(repositoryRoot, requestedPath);
        byte[] bytes;
        try
        {
            bytes = File.ReadAllBytes(path);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            throw Invalid("REQUEST_UNREADABLE", exception.Message);
        }

        if (bytes.Length == 0
            || bytes[^1] != (byte)'\n'
            || bytes.AsSpan().Contains((byte)'\r')
            || bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
        {
            throw Invalid(
                "REQUEST_ENCODING_INVALID",
                "request must be strict UTF-8 without BOM/CR and end in LF");
        }

        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw Invalid("REQUEST_ENCODING_INVALID", exception.Message);
        }

        TomlTable table;
        try
        {
            table = TomlSerializer.Deserialize<TomlTable>(text)
                ?? throw new FormatException("request is empty");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            throw Invalid("REQUEST_TOML_INVALID", exception.Message);
        }

        if (!table.Keys.ToImmutableHashSet(StringComparer.Ordinal).SetEquals(RequestKeys))
        {
            throw Invalid("REQUEST_KEYS_INVALID", "request keys are not canonical");
        }

        var atomId = RequiredString(table, "atom_id");
        var blockerClass = RequiredString(table, "blocker_class");
        var justification = RequiredString(table, "justification");
        var reentryCondition = RequiredString(table, "reentry_condition");
        if (!DigestionQuarantine.BlockerClasses.Contains(blockerClass, StringComparer.Ordinal))
        {
            throw Invalid(
                "BLOCKER_CLASS_UNKNOWN",
                $"blocker_class={blockerClass}; expected one of "
                + string.Join(',', DigestionQuarantine.BlockerClasses));
        }

        return new QuarantineRequest(atomId, blockerClass, justification, reentryCondition);
    }

    private static string RequiredString(TomlTable table, string key)
    {
        if (table[key] is not string value || string.IsNullOrWhiteSpace(value))
        {
            throw Invalid("REQUEST_VALUE_BLANK", $"key={key}");
        }

        return value.Trim();
    }

    private static string ResolveRequestPath(string repositoryRoot, string requestedPath)
    {
        if (string.IsNullOrWhiteSpace(requestedPath) || requestedPath != requestedPath.Trim())
        {
            throw Invalid("REQUEST_PATH_INVALID", "request path is blank or padded");
        }

        if (Path.IsPathFullyQualified(requestedPath))
        {
            return Path.GetFullPath(requestedPath);
        }

        var root = Path.GetFullPath(repositoryRoot);
        var resolved = Path.GetFullPath(Path.Combine(root, requestedPath));
        var rootPrefix = root.EndsWith(Path.DirectorySeparatorChar)
            ? root
            : root + Path.DirectorySeparatorChar;
        if (!resolved.StartsWith(rootPrefix, StringComparison.Ordinal))
        {
            throw Invalid("REQUEST_PATH_INVALID", "repository-relative request escapes the repository");
        }

        return resolved;
    }

    private static DigestionLedgerEntry LocateTarget(
        BackfillInventoryDocument document,
        string atomId)
    {
        var matches = document.RequireDigestionEntries()
            .Where(entry => string.Equals(entry.AtomId, atomId, StringComparison.Ordinal))
            .ToArray();
        return matches.Length switch
        {
            0 => throw Invalid("ATOM_ABSENT", $"atom_id={atomId}"),
            1 => matches[0],
            _ => throw Invalid("ATOM_AMBIGUOUS", $"atom_id={atomId} count={matches.Length}"),
        };
    }

    private static void RequireWritable(DigestionLedgerEntry entry)
    {
        if (entry.ProjectedStatus.Migration != DigestionMigrationState.Residual
            || entry.ProjectedStatus.Truth != DigestionTruthState.Open)
        {
            throw Invalid(
                "NOT_RESIDUAL_OPEN",
                $"atom_id={entry.AtomId} status="
                + DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                + "-"
                + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth));
        }

        if (!entry.CoverageGids.IsEmpty)
        {
            throw Invalid("COVERAGE_PRESENT", $"atom_id={entry.AtomId}");
        }

        if (entry.Receipts.CoverDisposition is not null)
        {
            throw Invalid("COVER_DISPOSITION_PRESENT", $"atom_id={entry.AtomId}");
        }
    }

    private static string LocateShard(RawRepositorySnapshot current, DigestionLedgerEntry entry)
    {
        var expected = $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/residual-open/{entry.AtomId}.yaml";
        return current.Entries.Count(item => string.Equals(item.Path, expected, StringComparison.Ordinal)) == 1
            ? expected
            : throw Invalid("SHARD_AMBIGUOUS", $"atom_id={entry.AtomId} path={expected}");
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot snapshot) =>
        SnapshotDecoder.Decode(snapshot) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new FormatException(failure.Message),
        };

    private static CommandResult Success(string line) =>
        new(true, line + "\n", string.Empty);

    private static InvalidOperationException Invalid(string code, string detail) =>
        new(code + " " + detail);

    private static QuarantineOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        string? request = null;
        string? clearAtomId = null;
        string? baseRevision = null;
        var replace = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--request" when request is null && index + 1 < arguments.Count:
                    request = arguments[++index];
                    break;
                case "--clear" when clearAtomId is null && index + 1 < arguments.Count:
                    clearAtomId = arguments[++index];
                    break;
                case "--base" when baseRevision is null && index + 1 < arguments.Count:
                    baseRevision = arguments[++index];
                    break;
                case "--replace" when !replace:
                    replace = true;
                    break;
                default:
                    throw Invalid("ARGUMENTS_INVALID", Usage);
            }
        }

        var set = request is not null && clearAtomId is null;
        var clear = clearAtomId is not null && request is null && !replace;
        if (baseRevision is null
            || string.IsNullOrWhiteSpace(baseRevision)
            || baseRevision != baseRevision.Trim()
            || !(set || clear))
        {
            throw Invalid("ARGUMENTS_INVALID", Usage);
        }

        return new QuarantineOptions(request, clearAtomId, baseRevision, replace);
    }

    private sealed record QuarantineOptions(
        string? RequestPath,
        string? ClearAtomId,
        string BaseRevision,
        bool Replace);

    private sealed record QuarantineRequest(
        string AtomId,
        string BlockerClass,
        string Justification,
        string ReentryCondition);
}

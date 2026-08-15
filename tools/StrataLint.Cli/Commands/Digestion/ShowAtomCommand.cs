using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ShowAtomCommand
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static CommandResult Run(
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var atomId = ParseArguments(arguments);
            var snapshot = Decode(repository.ReadCurrent());
            var document = BackfillInventoryLoader.Load(snapshot);
            var entries = document.RequireDigestionEntries()
                .Where(entry => entry.AtomId == atomId)
                .ToArray();
            var entry = entries.Length switch
            {
                1 => entries[0],
                0 => throw new FormatException(
                    $"atom_id {atomId} is absent from digestion ledger"),
                _ => throw new FormatException(
                    $"atom_id {atomId} is ambiguous in digestion ledger"),
            };
            var source = document.RequireDigestionSources()
                .Single(item => item.SourceId == entry.SourceId);
            var casBytes = ReadVerifiedCas(snapshot, entry);
            if (source.AcknowledgedStale.Contains(entry.AtomId, StringComparer.Ordinal))
            {
                return new CommandResult(true, Render(entry, casBytes, stale: true), string.Empty);
            }

            var replayedBytes = Replay(snapshot, source, entry);
            if (HasVerifiedCurrentGeneration(snapshot, source, entry, replayedBytes))
            {
                return new CommandResult(true, Render(entry, casBytes, stale: true), string.Empty);
            }

            VerifyReplay(entry, replayedBytes, casBytes);
            return new CommandResult(true, Render(entry, replayedBytes, stale: false), string.Empty);
        }
        catch (Exception exception) when (
            exception is FormatException
                or InvalidOperationException
                or IOException
                or ArgumentException
                or DecoderFallbackException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"SHOW_ATOM_INVALID {exception.Message}\n");
        }
    }

    private static string ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 2
            || arguments[0] != "--atom-id"
            || string.IsNullOrWhiteSpace(arguments[1]))
        {
            throw new InvalidOperationException("USAGE: StrataLint show-atom --atom-id ATOM_ID");
        }

        return arguments[1];
    }

    private static ImmutableArray<byte> Replay(
        RepositorySnapshot snapshot,
        DigestionLedgerSource source,
        DigestionLedgerEntry entry)
    {
        if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile))
        {
            throw new FormatException(
                $"atom {entry.AtomId} source is missing: {source.SourcePath}");
        }

        if (DigestionSourceConflictMarkers.FindFirstLine(sourceFile.RawBytes.AsSpan()) is { } line)
        {
            throw new FormatException(
                DigestionSourceConflictMarkers.FormatFinding(source.SourcePath, line));
        }

        if (source.Atomizer == AtomizerRegistry.NoAtomizerId)
        {
            var boundary = entry.Boundary
                ?? throw new FormatException(
                    $"atom {entry.AtomId} has no boundary for atomizer none");
            if (boundary.StartByte < 0
                || boundary.EndByte <= boundary.StartByte
                || boundary.EndByte > sourceFile.RawBytes.Length)
            {
                throw new FormatException(
                    $"atom {entry.AtomId} boundary is outside {source.SourcePath}");
            }

            return ImmutableArray.CreateRange(
                sourceFile.RawBytes.AsSpan()[boundary.StartByte..boundary.EndByte].ToArray());
        }

        var rules = TheoryAtomizerDataLoader.Load(snapshot);
        var replayed = AtomizerRegistry.Atomize(
            source.Atomizer,
            sourceFile.RawBytes.AsSpan(),
            rules);
        return replayed.ResolveClaim(entry.AstPath).RawBytes;
    }

    private static ImmutableArray<byte> ReadVerifiedCas(
        RepositorySnapshot snapshot,
        DigestionLedgerEntry entry)
    {
        if (!DigestionFingerprint.IsCanonicalSha256(entry.CasRef))
        {
            throw new FormatException(
                $"atom {entry.AtomId} cas_ref is not canonical: {entry.CasRef}");
        }

        if (!DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.RawSha256)
            || !DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.NormalizedSha256))
        {
            throw new FormatException(
                $"atom {entry.AtomId} ledger fingerprints are not canonical");
        }

        var casPath = DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..];
        if (!snapshot.TryGetFile(casPath, out var casBlob))
        {
            throw new FormatException(
                $"atom {entry.AtomId} CAS blob is missing: {casPath}");
        }

        var capturedCas = DigestionCasStore.Capture(casBlob.RawBytes.AsSpan());
        if (capturedCas.Reference != entry.CasRef)
        {
            throw new FormatException(
                $"atom {entry.AtomId} CAS blob hash mismatch: expected {entry.CasRef}, "
                + $"actual {capturedCas.Reference}");
        }

        var capturedFingerprints = DigestionFingerprint.Compute(casBlob.RawBytes.AsSpan());
        if (capturedFingerprints.RawSha256 != entry.Fingerprints.RawSha256)
        {
            throw new FormatException(
                $"atom {entry.AtomId} CAS raw hash mismatch: expected "
                + $"{entry.Fingerprints.RawSha256}, actual {capturedFingerprints.RawSha256}");
        }

        if (capturedFingerprints.NormalizedSha256 != entry.Fingerprints.NormalizedSha256)
        {
            throw new FormatException(
                $"atom {entry.AtomId} CAS normalized hash mismatch: expected "
                + $"{entry.Fingerprints.NormalizedSha256}, actual "
                + capturedFingerprints.NormalizedSha256);
        }

        if (capturedFingerprints.RawSha256 != entry.CasRef)
        {
            throw new FormatException(
                $"atom {entry.AtomId} CAS bytes mismatch cas_ref {entry.CasRef}");
        }

        return casBlob.RawBytes;
    }

    private static bool HasVerifiedCurrentGeneration(
        RepositorySnapshot snapshot,
        DigestionLedgerSource source,
        DigestionLedgerEntry requested,
        ImmutableArray<byte> replayedBytes)
    {
        var replayed = DigestionFingerprint.Compute(replayedBytes.AsSpan());
        var replacements = source.Entries.Where(entry =>
                entry.AtomId != requested.AtomId
                && entry.AstPath == requested.AstPath
                && entry.Fingerprints == replayed
                && entry.CasRef == replayed.RawSha256)
            .ToArray();
        if (replacements.Length == 0)
        {
            return false;
        }

        if (replacements.Length > 1)
        {
            throw new FormatException(
                $"atom {requested.AtomId} current generation is ambiguous at {requested.AstPath}");
        }

        var replacementCas = ReadVerifiedCas(snapshot, replacements[0]);
        VerifyReplay(replacements[0], replayedBytes, replacementCas);
        return true;
    }

    private static void VerifyReplay(
        DigestionLedgerEntry entry,
        ImmutableArray<byte> replayedBytes,
        ImmutableArray<byte> casBytes)
    {
        var replayed = DigestionFingerprint.Compute(replayedBytes.AsSpan());
        if (replayed.RawSha256 != entry.Fingerprints.RawSha256)
        {
            throw new FormatException(
                $"atom {entry.AtomId} raw hash mismatch: expected "
                + $"{entry.Fingerprints.RawSha256}, actual {replayed.RawSha256}");
        }

        if (replayed.NormalizedSha256 != entry.Fingerprints.NormalizedSha256)
        {
            throw new FormatException(
                $"atom {entry.AtomId} normalized hash mismatch: expected "
                + $"{entry.Fingerprints.NormalizedSha256}, actual {replayed.NormalizedSha256}");
        }

        if (replayed.RawSha256 != entry.CasRef
            || !replayedBytes.AsSpan().SequenceEqual(casBytes.AsSpan()))
        {
            throw new FormatException(
                $"atom {entry.AtomId} replayed bytes mismatch cas_ref {entry.CasRef}");
        }
    }

    private static string Render(
        DigestionLedgerEntry entry,
        ImmutableArray<byte> rawBytes,
        bool stale)
    {
        var rawText = StrictUtf8.GetString(rawBytes.AsSpan());
        var normalizedText = DigestionFingerprint.NormalizeText(rawBytes.AsSpan());
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine(
            $"SHOW_ATOM atom_id={entry.AtomId} source_id={entry.SourceId} "
            + $"source_path={entry.SourcePath} atomizer={entry.Atomizer} ast_path={entry.AstPath}");
        if (stale)
        {
            writer.WriteLine("STALE_READ status=stale source=cas");
        }

        writer.WriteLine(
            $"HASH_VERIFY raw_sha256={entry.Fingerprints.RawSha256} "
            + $"normalized_sha256={entry.Fingerprints.NormalizedSha256} "
            + $"cas_ref={entry.CasRef} status=match");
        WriteText(writer, "RAW", rawText);
        WriteText(writer, "NORMALIZED", normalizedText);
        return writer.ToString();
    }

    private static void WriteText(StringWriter writer, string label, string value)
    {
        writer.WriteLine($"BEGIN_{label}_TEXT");
        writer.Write(value);
        if (!value.EndsWith('\n'))
        {
            writer.WriteLine();
        }
        writer.WriteLine($"END_{label}_TEXT");
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
}

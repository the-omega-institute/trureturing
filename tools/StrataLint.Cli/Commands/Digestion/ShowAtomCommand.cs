using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
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
            var casBytes = ReadCommittedCas(snapshot, entry);
            var entryIndex = source.Entries.IndexOf(entry);
            var stale = source.AcknowledgedStale.Contains(entry.AtomId, StringComparer.Ordinal)
                || source.Entries
                    .Skip(entryIndex + 1)
                    .Any(candidate => candidate.AstPath == entry.AstPath);
            var selfFormalization = CurrentFormalizationReceipt(entry, snapshot);
            var parentFormalizations = document.RequireDigestionEntries()
                .Where(parent => parent.Receipts.ChainAtoms.Contains(entry.AtomId, StringComparer.Ordinal))
                .OrderBy(static parent => parent.AtomId, StringComparer.Ordinal)
                .Select(parent => ParentFormalization(parent, snapshot))
                .ToImmutableArray();
            return new CommandResult(true, Render(entry, casBytes, stale,
                selfFormalization, parentFormalizations), string.Empty);
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

    private static ImmutableArray<byte> ReadCommittedCas(
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

        return casBlob.RawBytes;
    }

    private static string Render(
        DigestionLedgerEntry entry,
        ImmutableArray<byte> rawBytes,
        bool stale, DigestionFormalizationReceipt? selfFormalization,
        ImmutableArray<ParentFormalizationPointer> parentFormalizations)
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
            $"HASH_RECORD raw_sha256={entry.Fingerprints.RawSha256} "
            + $"normalized_sha256={entry.Fingerprints.NormalizedSha256} "
            + $"cas_ref={entry.CasRef} source=ledger");
        writer.WriteLine("FORMALIZATION_POINTERS");
        if (selfFormalization is not null) { writer.WriteLine(
            $"SELF_FORMALIZATION status=available primary_gid={selfFormalization.PrimaryGid} "
            + $"receipt_path={CanonicalReceiptPath(entry.AtomId)}"); }
        if (parentFormalizations.IsEmpty) { writer.WriteLine("PARENT_FORMALIZATIONS status=no-parent"); }

        foreach (var parent in parentFormalizations)
        {
            if (parent.PrimaryGid is not null) { writer.WriteLine(
                $"PARENT_FORMALIZATION parent_atom_id={parent.ParentAtomId} status=available "
                + $"primary_gid={parent.PrimaryGid} receipt_path={parent.ReceiptPath}"); continue; }
            writer.WriteLine($"PARENT_FORMALIZATION parent_atom_id={parent.ParentAtomId} "
                + $"status={parent.Status} receipt_path={parent.ReceiptPath}");
        }

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
    private static DigestionFormalizationReceipt? CurrentFormalizationReceipt(
        DigestionLedgerEntry entry, RepositorySnapshot snapshot)
    {
        var path = CanonicalReceiptPath(entry.AtomId);
        if (!DigestionFormalizationReceipt.IsCanonicalPath(path) || !snapshot.TryGetFile(path, out _)) { return null; }
        DigestionFormalizationReceipt? receipt = null;
        LoadFormalizationReceipt(snapshot, path, out receipt);
        if (receipt is null) { return null; }
        if (!string.Equals(receipt!.AtomId, entry.AtomId, StringComparison.Ordinal)
            || !string.Equals(receipt.CasRef, entry.CasRef, StringComparison.Ordinal)
            || !string.Equals(receipt.RawSha256, entry.Fingerprints.RawSha256, StringComparison.Ordinal))
        { return null; }
        return receipt;
    }
    private static void LoadFormalizationReceipt(RepositorySnapshot snapshot, string path,
        out DigestionFormalizationReceipt? receipt)
    {
        try { receipt = DigestionFormalizationReceipt.Load(snapshot, path); }
        catch (Exception exception) when (exception is FormatException or JsonException)
        { receipt = null; }
    }
    private static ParentFormalizationPointer ParentFormalization(
        DigestionLedgerEntry parent, RepositorySnapshot snapshot)
    {
        var path = CanonicalReceiptPath(parent.AtomId);
        if (!snapshot.TryGetFile(path, out _)) { return new(parent.AtomId, "parent-without-receipt", null, path); }
        var formalization = CurrentFormalizationReceipt(parent, snapshot);
        if (formalization is null) { return new(parent.AtomId, "parent-receipt-unavailable", null, path); }
        return new(parent.AtomId, "available", formalization!.PrimaryGid, path);
    }
    private static string CanonicalReceiptPath(string atomId) => DigestionFormalizationReceipt.RootPath
        + atomId + DigestionFormalizationReceipt.PathSuffix;

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private sealed record ParentFormalizationPointer(
        string ParentAtomId, string Status, string? PrimaryGid, string ReceiptPath);
}

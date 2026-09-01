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
            var stale = source.AcknowledgedStale.Contains(entry.AtomId, StringComparer.Ordinal);
            var selfFormalization = FormalizationPointer(entry, snapshot);
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
        bool stale,
        FormalizationReceiptPointer selfFormalization,
        ImmutableArray<FormalizationReceiptPointer> parentFormalizations)
    {
        var rawText = StrictUtf8.GetString(rawBytes.AsSpan());
        var normalizedText = DigestionFingerprint.NormalizeText(rawBytes.AsSpan());
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine(
            $"SHOW_ATOM atom_id={entry.AtomId} source_id={entry.SourceId} "
            + $"source_path={entry.SourcePath} atomizer={entry.Atomizer}");
        if (stale)
        {
            writer.WriteLine("STALE_READ status=stale source=cas");
        }

        writer.WriteLine(
            $"HASH_RECORD raw_sha256={entry.Fingerprints.RawSha256} "
            + $"normalized_sha256={entry.Fingerprints.NormalizedSha256} "
            + $"cas_ref={entry.CasRef} source=ledger");
        writer.WriteLine("FORMALIZATION_POINTERS");
        writer.WriteLine(selfFormalization switch
        {
            FormalizationReceiptPointer.Available available =>
                "SELF_FORMALIZATION_POINTER status=available "
                + $"primary_gid={available.PrimaryGid} "
                + $"gids={string.Join(',', available.Gids)} "
                + $"receipt_path={available.ReceiptPath}",
            FormalizationReceiptPointer.Unavailable unavailable => unavailable.Reason switch
            {
                FormalizationReceiptUnavailability.MissingReceipt =>
                    "SELF_FORMALIZATION_POINTER status=self-without-receipt "
                    + $"receipt_path={unavailable.ReceiptPath}",
                FormalizationReceiptUnavailability.UnusableReceipt =>
                    "SELF_FORMALIZATION_POINTER status=self-receipt-unavailable "
                    + $"receipt_path={unavailable.ReceiptPath}",
                _ => throw new InvalidOperationException(
                    "unknown self formalization receipt unavailability"),
            },
            _ => throw new InvalidOperationException("unknown self formalization pointer"),
        });

        if (parentFormalizations.IsEmpty)
        {
            writer.WriteLine("PARENT_FORMALIZATIONS status=no-parent");
        }

        foreach (var parent in parentFormalizations)
        {
            writer.WriteLine(parent switch
            {
                FormalizationReceiptPointer.Available available =>
                    $"PARENT_FORMALIZATION_POINTER parent_atom_id={available.AtomId} "
                    + "status=available "
                    + $"primary_gid={available.PrimaryGid} "
                    + $"gids={string.Join(',', available.Gids)} "
                    + $"receipt_path={available.ReceiptPath}",
                FormalizationReceiptPointer.Unavailable unavailable => unavailable.Reason switch
                {
                    FormalizationReceiptUnavailability.MissingReceipt =>
                        $"PARENT_FORMALIZATION_POINTER parent_atom_id={unavailable.AtomId} "
                        + "status=parent-without-receipt "
                        + $"receipt_path={unavailable.ReceiptPath}",
                    FormalizationReceiptUnavailability.UnusableReceipt =>
                        $"PARENT_FORMALIZATION_POINTER parent_atom_id={unavailable.AtomId} "
                        + "status=parent-receipt-unavailable "
                        + $"receipt_path={unavailable.ReceiptPath}",
                    _ => throw new InvalidOperationException(
                        "unknown parent formalization receipt unavailability"),
                },
                _ => throw new InvalidOperationException("unknown parent formalization pointer"),
            });
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

    private static FormalizationReceiptPointer FormalizationPointer(
        DigestionLedgerEntry entry,
        RepositorySnapshot snapshot)
    {
        var path = DigestionFormalizationReceipt.PathForAtom(entry.AtomId);
        if (!snapshot.TryGetFile(path, out _))
        {
            return new FormalizationReceiptPointer.Unavailable(
                entry.AtomId,
                FormalizationReceiptUnavailability.MissingReceipt,
                path);
        }

        var receipt = BoundFormalizationReceipt(entry, snapshot, path);
        if (receipt is not null)
        {
            return new FormalizationReceiptPointer.Available(
                entry.AtomId,
                receipt.PrimaryGid,
                receipt.RegisteredGids,
                path);
        }

        return new FormalizationReceiptPointer.Unavailable(
            entry.AtomId,
            FormalizationReceiptUnavailability.UnusableReceipt,
            path);
    }

    private static DigestionFormalizationReceipt? BoundFormalizationReceipt(
        DigestionLedgerEntry entry,
        RepositorySnapshot snapshot,
        string path)
    {
        if (!DigestionFormalizationReceipt.IsCanonicalPath(path))
        {
            return null;
        }

        try
        {
            var receipt = DigestionFormalizationReceipt.Load(snapshot, path);
            if (!string.Equals(receipt.AtomId, entry.AtomId, StringComparison.Ordinal))
            {
                return null;
            }

            if (!string.Equals(receipt.CasRef, entry.CasRef, StringComparison.Ordinal))
            {
                return null;
            }

            if (!string.Equals(
                    receipt.RawSha256,
                    entry.Fingerprints.RawSha256,
                    StringComparison.Ordinal))
            {
                return null;
            }

            return receipt;
        }
        catch (FormatException)
        {
            return null;
        }
        catch (JsonException)
        {
            return null;
        }
        catch (InvalidOperationException)
        {
            return null;
        }
    }

    private static FormalizationReceiptPointer ParentFormalization(
        DigestionLedgerEntry parent,
        RepositorySnapshot snapshot) => FormalizationPointer(parent, snapshot);

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private enum FormalizationReceiptUnavailability
    {
        MissingReceipt,
        UnusableReceipt,
    }

    private abstract record FormalizationReceiptPointer(string AtomId, string ReceiptPath)
    {
        internal sealed record Available(
            string AtomId,
            string PrimaryGid,
            ImmutableArray<string> Gids,
            string ReceiptPath) : FormalizationReceiptPointer(AtomId, ReceiptPath);

        internal sealed record Unavailable(
            string AtomId,
            FormalizationReceiptUnavailability Reason,
            string ReceiptPath) : FormalizationReceiptPointer(AtomId, ReceiptPath);
    }
}

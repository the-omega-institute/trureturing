using StrataLint.Engine;

namespace StrataLint.Cli;

// Emit a canonical digestion-formalization-v1 receipt (spec §4a "pre-committed
// signature"). The formalizer runs this in PR-1 — after writing the intended Lean
// declaration and producing the raw Lean report — to pin the atom -> declaration
// binding: atom_id + primary_gid + the atom's content fingerprint (read from
// BACKFILL) + the declaration's canonical signature (name_key/kind/type, read from
// the current raw Lean report). The receipt is committed alongside the
// formalization; the cover transaction (PR-2) then admits the deposit only when
// the deposited declaration's signature still equals this pinned signature.
//
// Anti-swap value: because the signature is read from the report at emit time, the
// receipt records exactly the declaration PR-1 formalized; if it is changed
// between PR-1 and PR-2, cover's signature-match rejects. Hollow-fidelity (the
// pinned signature itself being vacuous) remains the deferred §4(b) attestation.
//
// This command is the producer; cover-atom is the consumer. It writes canonical
// bytes via DigestionFormalizationReceipt.Write and never mutates BACKFILL.
internal static class EmitFormalizationReceiptCommand
{
    internal const string DefaultOutputPrefix = "Meta/Digestion/formalizations/";

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var options = ParseArguments(arguments);

            // Gate: the primary GID must select a Lean declaration, not a module.
            if (!Gid.TryParse(options.Gid, out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: not null })
            {
                throw new InvalidOperationException(
                    $"receipt GID must select a Lean declaration: {options.Gid}");
            }

            var current = Decode(repository.ReadCurrent());
            var document = LoadDocument(current);

            // Gate: the atom must exist in BACKFILL exactly once; its content
            // fingerprint (cas_ref / raw_sha256) is read here so the receipt binds
            // to the atom's actual content (fail-closed if absent/ambiguous).
            var entry = LocateAtom(document, options.AtomId);

            // Resolve the declaration's canonical signature from the current raw Lean
            // report (fail-closed if the declaration is missing/ambiguous there).
            var report = leanReportSource.Load(current);
            var signature = DigestionFormalizationReceipt.ResolveSignature(gid, report);

            var receipt = new DigestionFormalizationReceipt(
                options.AtomId,
                options.Gid,
                signature,
                entry.CasRef,
                entry.Fingerprints.RawSha256);
            var bytes = DigestionFormalizationReceipt.Write(receipt);

            var relativeOut = options.OutPath ?? DefaultOutputPrefix + options.AtomId + ".v1.json";
            var outputPath = Path.Combine(
                Path.GetFullPath(repositoryRoot),
                relativeOut.Replace('/', Path.DirectorySeparatorChar));
            var directory = Path.GetDirectoryName(outputPath)
                ?? throw new InvalidOperationException("receipt output path has no parent directory");
            Directory.CreateDirectory(directory);
            IngestCommand.ReplaceLedgerAtomically(outputPath, bytes.AsSpan());

            return new CommandResult(
                true,
                $"FORMALIZATION_RECEIPT atom_id={options.AtomId} gid={options.Gid} "
                + $"out={relativeOut} "
                + $"signature=({signature.NameKey}, {signature.Kind}, {signature.Type})\n",
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"FORMALIZATION_RECEIPT_INVALID {exception.Message}\n");
        }
    }

    private static DigestionLedgerEntry LocateAtom(BackfillInventoryDocument document, string atomId)
    {
        var matches = document.RequireDigestionEntries()
            .Where(entry => string.Equals(entry.AtomId, atomId, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length == 0)
        {
            throw new InvalidOperationException($"receipt atom {atomId} is absent from the ledger");
        }

        if (matches.Length > 1)
        {
            throw new InvalidOperationException($"receipt atom {atomId} is ambiguous in the ledger");
        }

        return matches[0];
    }

    private sealed record ReceiptArguments(string AtomId, string Gid, string? OutPath);

    private static ReceiptArguments ParseArguments(IReadOnlyList<string> arguments)
    {
        string? atomId = null;
        string? gid = null;
        string? outPath = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count)
            {
                throw Usage();
            }

            switch (arguments[index])
            {
                case "--atom-id" when atomId is null:
                    atomId = arguments[index + 1];
                    break;
                case "--gid" when gid is null:
                    gid = arguments[index + 1];
                    break;
                case "--out" when outPath is null:
                    outPath = arguments[index + 1];
                    break;
                default:
                    throw Usage();
            }
        }

        if (string.IsNullOrWhiteSpace(atomId) || string.IsNullOrWhiteSpace(gid))
        {
            throw Usage();
        }

        return new ReceiptArguments(atomId, gid, string.IsNullOrWhiteSpace(outPath) ? null : outPath);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint emit-formalization-receipt --atom-id ATOM_ID --gid DECL_GID "
        + "[--out RECEIPT_PATH]");

    private static BackfillInventoryDocument LoadDocument(RepositorySnapshot snapshot) =>
        BackfillInventoryLoader.Load(snapshot);

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
}

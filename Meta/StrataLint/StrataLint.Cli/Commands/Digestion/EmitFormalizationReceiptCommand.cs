using System.Collections.Immutable;
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

            // Gate: the primary and every hosted-extension GID must select a Lean
            // declaration, not a module.
            var gids = options.Gids.Select(gidText =>
            {
                if (!Gid.TryParse(gidText, out var gid)
                    || gid.ToTarget() is not Target.Formal { Declaration: not null })
                {
                    throw new InvalidOperationException(
                        $"receipt GID must select a Lean declaration: {gidText}");
                }

                return gid;
            }).ToArray();
            var primaryGid = gids[0];

            var current = Decode(repository.ReadCurrent());
            var document = LoadDocument(current);

            // Gate: the atom must exist in BACKFILL exactly once; its content
            // fingerprint (cas_ref / raw_sha256) is read here so the receipt binds
            // to the atom's actual content (fail-closed if absent/ambiguous).
            var entry = LocateAtom(document, options.AtomId);
            if (options.RequireExistingCoverage
                && !entry.CoverageGids.Contains(primaryGid.Value, StringComparer.Ordinal))
            {
                throw new InvalidOperationException(
                    $"receipt primary GID {primaryGid.Value} is not already bound to atom {options.AtomId}");
            }

            // Resolve signatures from the current report. If an atom receipt already
            // exists, every old pin is immutable: hosted deposit may append a new
            // secondary pin but may not rewrite the primary or an earlier extension.
            var report = leanReportSource.Load(current);
            var signature = DigestionFormalizationReceipt.ResolveSignature(primaryGid, report);
            var extensions = new Dictionary<string, DigestionFormalizationExtension>(StringComparer.Ordinal);
            var canonicalReceiptPath = DefaultOutputPrefix + options.AtomId + ".v1.json";
            if (current.TryGetFile(canonicalReceiptPath, out _))
            {
                var existing = DigestionFormalizationReceipt.Load(current, canonicalReceiptPath);
                RequireExistingReceiptBinding(existing, entry, primaryGid.Value);
                RequireUnchangedSignature(primaryGid, signature, existing.Signature);
                foreach (var extension in existing.HostedExtensions)
                {
                    if (!Gid.TryParse(extension.Gid, out var extensionGid))
                    {
                        throw new InvalidOperationException(
                            $"existing hosted extension GID is invalid: {extension.Gid}");
                    }

                    var currentSignature = DigestionFormalizationReceipt.ResolveSignature(extensionGid, report);
                    RequireUnchangedSignature(extensionGid, currentSignature, extension.Signature);
                    extensions.Add(extension.Gid, extension);
                }
            }
            else if (gids.Length > 1)
            {
                throw new InvalidOperationException(
                    $"hosted extension requires an existing formalization receipt: {canonicalReceiptPath}");
            }

            foreach (var secondaryGid in gids.Skip(1))
            {
                var secondarySignature = DigestionFormalizationReceipt.ResolveSignature(secondaryGid, report);
                if (extensions.TryGetValue(secondaryGid.Value, out var existing))
                {
                    RequireUnchangedSignature(secondaryGid, secondarySignature, existing.Signature);
                    continue;
                }

                extensions.Add(
                    secondaryGid.Value,
                    new DigestionFormalizationExtension(secondaryGid.Value, secondarySignature));
            }

            var receipt = new DigestionFormalizationReceipt(
                options.AtomId,
                primaryGid.Value,
                signature,
                entry.CasRef,
                entry.Fingerprints.RawSha256,
                extensions.Values.OrderBy(static extension => extension.Gid, StringComparer.Ordinal).ToImmutableArray());
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
                $"FORMALIZATION_RECEIPT atom_id={options.AtomId} gid={primaryGid.Value} "
                + $"hosted_extensions={extensions.Count} "
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

    private static void RequireExistingReceiptBinding(
        DigestionFormalizationReceipt receipt,
        DigestionLedgerEntry entry,
        string primaryGid)
    {
        if (!string.Equals(receipt.AtomId, entry.AtomId, StringComparison.Ordinal)
            || !string.Equals(receipt.PrimaryGid, primaryGid, StringComparison.Ordinal)
            || !string.Equals(receipt.CasRef, entry.Fingerprints.RawSha256, StringComparison.Ordinal)
            || !string.Equals(receipt.RawSha256, entry.Fingerprints.RawSha256, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"existing formalization receipt conflicts with atom/GID: {entry.AtomId}");
        }
    }

    private static void RequireUnchangedSignature(
        Gid gid,
        DigestionFormalizationSignature current,
        DigestionFormalizationSignature pinned)
    {
        if (current != pinned)
        {
            throw new InvalidOperationException(
                $"existing formalization receipt signature changed for {gid.Value}");
        }
    }

    private sealed record ReceiptArguments(
        string AtomId,
        ImmutableArray<string> Gids,
        string? OutPath,
        bool RequireExistingCoverage);

    private static ReceiptArguments ParseArguments(IReadOnlyList<string> arguments)
    {
        string? atomId = null;
        var gids = ImmutableArray.CreateBuilder<string>();
        string? outPath = null;
        bool? requireExistingCoverage = null;
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
                case "--gid":
                    gids.Add(arguments[index + 1]);
                    break;
                case "--out" when outPath is null:
                    outPath = arguments[index + 1];
                    break;
                case "--require-existing-coverage" when requireExistingCoverage is null
                    && bool.TryParse(arguments[index + 1], out var required):
                    requireExistingCoverage = required;
                    break;
                default:
                    throw Usage();
            }
        }

        if (string.IsNullOrWhiteSpace(atomId)
            || gids.Count == 0
            || gids.Any(string.IsNullOrWhiteSpace)
            || gids.Distinct(StringComparer.Ordinal).Count() != gids.Count)
        {
            throw Usage();
        }

        return new ReceiptArguments(
            atomId,
            gids.ToImmutable(),
            string.IsNullOrWhiteSpace(outPath) ? null : outPath,
            requireExistingCoverage ?? false);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint emit-formalization-receipt --atom-id ATOM_ID --gid PRIMARY_GID "
        + "[--gid SECONDARY_GID ...] "
        + "[--out RECEIPT_PATH] [--require-existing-coverage true|false]");

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

using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

// Emit a canonical digestion-formalization-v1 receipt (spec §11.21 "pre-committed
// signature"). The formalizer runs this in PR-1 — after writing the intended Lean
// declaration and producing the raw Lean report — to pin atom_id + the first
// registered GID + ordered hosted extensions + the atom's content fingerprint
// (read from BACKFILL) + each declaration's canonical signature
// (name_key/kind/type, read from the current raw Lean report). The receipt is
// committed alongside the
// formalization; the cover transaction (PR-2) then admits the deposit only when
// the deposited declaration's signature still equals this pinned signature.
//
// Anti-swap value: because the signature is read from the report at emit time, the
// receipt records exactly the declaration PR-1 formalized; if it is changed
// between PR-1 and PR-2, cover's signature-match rejects. Hollow-fidelity (the
// pinned signature itself being vacuous) remains the deferred §11.21
// hollow-fidelity attestation.
//
// This command is the producer; cover-atom is the consumer. It writes canonical
// bytes via DigestionFormalizationReceipt.Write and never mutates BACKFILL.
internal static class EmitFormalizationReceiptCommand
{
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
            var relativeOut = options.OutPath ?? DigestionFormalizationReceipt.PathForAtom(options.AtomId);
            var outputPath = ResolveOutputPath(repositoryRoot, options.AtomId, relativeOut);

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
            var current = Decode(repository.ReadCurrent());
            var document = LoadDocument(current);

            // Gate: the atom must exist in BACKFILL exactly once; its content
            // fingerprint (cas_ref / raw_sha256) is read here so the receipt binds
            // to the atom's actual content (fail-closed if absent/ambiguous).
            var entry = LocateAtom(document, options.AtomId);

            // Resolve signatures from the current report. If an atom receipt already
            // exists, every old pin is immutable: hosted deposit may append a new
            // secondary pin but may not rewrite the primary or an earlier extension.
            var report = leanReportSource.Load(current);
            var extensions = new Dictionary<string, DigestionFormalizationExtension>(StringComparer.Ordinal);
            var canonicalReceiptPath = DigestionFormalizationReceipt.PathForAtom(options.AtomId);
            var reanchoredPaths = ImmutableHashSet.CreateBuilder<RepoPath>();
            DigestionFormalizationReceipt? existingReceipt = null;
            Gid primaryGid;
            DigestionFormalizationSignature signature;
            if (current.TryGetFile(canonicalReceiptPath, out _))
            {
                var existing = DigestionFormalizationReceipt.Load(current, canonicalReceiptPath);
                existingReceipt = existing;
                if (options.ReanchorSignature)
                {
                    RequireReanchorAtomBinding(existing, entry);
                }

                RequireExistingReceiptBinding(existing, entry);
                if (!Gid.TryParse(existing.PrimaryGid, out var existingPrimaryGid))
                {
                    throw new InvalidOperationException(
                        $"existing formalization receipt primary GID is invalid: {existing.PrimaryGid}");
                }

                primaryGid = existingPrimaryGid;
                signature = DigestionFormalizationReceipt.ResolveSignature(primaryGid, report);
                RequireUnchangedSignature(
                    primaryGid,
                    signature,
                    existing.Signature,
                    options.ReanchorSignature,
                    reanchoredPaths);
                foreach (var extension in existing.HostedExtensions)
                {
                    if (!Gid.TryParse(extension.Gid, out var extensionGid))
                    {
                        throw new InvalidOperationException(
                            $"existing hosted extension GID is invalid: {extension.Gid}");
                    }

                    var currentSignature = DigestionFormalizationReceipt.ResolveSignature(extensionGid, report);
                    RequireUnchangedSignature(
                        extensionGid,
                        currentSignature,
                        extension.Signature,
                        options.ReanchorSignature,
                        reanchoredPaths);
                    extensions.Add(extension.Gid, extension);
                }
            }
            else
            {
                if (options.ReanchorSignature)
                {
                    throw new InvalidOperationException(
                        "reanchor requires an existing canonical formalization receipt");
                }

                primaryGid = gids[0];
                signature = DigestionFormalizationReceipt.ResolveSignature(primaryGid, report);
            }

            foreach (var secondaryGid in gids.Where(gid =>
                         !string.Equals(gid.Value, primaryGid.Value, StringComparison.Ordinal)))
            {
                var secondarySignature = DigestionFormalizationReceipt.ResolveSignature(secondaryGid, report);
                if (extensions.TryGetValue(secondaryGid.Value, out var existing))
                {
                    RequireUnchangedSignature(
                        secondaryGid,
                        secondarySignature,
                        existing.Signature,
                        options.ReanchorSignature,
                        reanchoredPaths);
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
            if (existingReceipt is not null && options.ReanchorSignature)
            {
                RequireReanchorReceiptBinding(existingReceipt, receipt);
                if (reanchoredPaths.Count > 0)
                {
                    var protectedBase = Decode(repository.ReadRevision(options.BaselineRevision!));
                    RequireEquivalentPropositionSources(
                        protectedBase,
                        current,
                        report,
                        reanchoredPaths.ToImmutable());
                }
            }

            var bytes = DigestionFormalizationReceipt.Write(receipt);

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
        DigestionLedgerEntry entry)
    {
        if (!string.Equals(receipt.AtomId, entry.AtomId, StringComparison.Ordinal)
            || !string.Equals(receipt.CasRef, entry.Fingerprints.RawSha256, StringComparison.Ordinal)
            || !string.Equals(receipt.RawSha256, entry.Fingerprints.RawSha256, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"existing formalization receipt conflicts with atom: {entry.AtomId}");
        }
    }

    private static void RequireUnchangedSignature(
        Gid gid,
        DigestionFormalizationSignature current,
        DigestionFormalizationSignature pinned,
        bool reanchorSignature,
        ImmutableHashSet<RepoPath>.Builder reanchoredPaths)
    {
        if (current == pinned)
        {
            return;
        }

        if (!reanchorSignature)
        {
            throw new InvalidOperationException(
                $"existing formalization receipt signature changed for {gid.Value}");
        }

        if (!string.Equals(current.NameKey, pinned.NameKey, StringComparison.Ordinal)
            || !string.Equals(current.Kind, pinned.Kind, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"reanchor requires unchanged signature name_key and kind for {gid.Value}");
        }

        reanchoredPaths.Add(gid.Path);
    }

    private static void RequireReanchorAtomBinding(
        DigestionFormalizationReceipt receipt,
        DigestionLedgerEntry entry)
    {
        if (!string.Equals(receipt.AtomId, entry.AtomId, StringComparison.Ordinal)
            || !string.Equals(receipt.CasRef, entry.Fingerprints.RawSha256, StringComparison.Ordinal)
            || !string.Equals(receipt.RawSha256, entry.Fingerprints.RawSha256, StringComparison.Ordinal))
        {
            throw ReanchorBindingChanged();
        }
    }

    private static void RequireReanchorReceiptBinding(
        DigestionFormalizationReceipt existing,
        DigestionFormalizationReceipt replacement)
    {
        var existingExtensionGids = existing.HostedExtensions
            .Select(static extension => extension.Gid)
            .ToHashSet(StringComparer.Ordinal);
        var replacementExtensionGids = replacement.HostedExtensions
            .Select(static extension => extension.Gid)
            .ToHashSet(StringComparer.Ordinal);
        if (!string.Equals(existing.AtomId, replacement.AtomId, StringComparison.Ordinal)
            || !string.Equals(existing.CasRef, replacement.CasRef, StringComparison.Ordinal)
            || !string.Equals(existing.RawSha256, replacement.RawSha256, StringComparison.Ordinal)
            || !string.Equals(existing.PrimaryGid, replacement.PrimaryGid, StringComparison.Ordinal)
            || !existingExtensionGids.SetEquals(replacementExtensionGids))
        {
            throw ReanchorBindingChanged();
        }
    }

    private static InvalidOperationException ReanchorBindingChanged() => new(
        "reanchor requires unchanged atom and GID bindings "
        + "(atom_id/cas_ref/raw_sha256/primary_gid/hosted_extensions gid set)");

    private static void RequireEquivalentPropositionSources(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        LeanAxiomReport report,
        ImmutableHashSet<RepoPath> reanchoredPaths)
    {
        var equivalent = false;
        string? failureDetail = null;
        try
        {
            var baseView = FrozenLedgerBaseViewReader.Read(protectedBase);
            var truth = DagLedgerCommandPreparation.BuildTruth(candidate, report);
            var states = LeanTruthStates.Resolve(candidate, truth.Lean);
            var adjacency = LeanImportAdjacency.Build(candidate, truth.Lean);
            var candidateCatalog = FrozenContentAddress.BuildAdmissionCatalog(
                candidate,
                truth.Lean,
                states,
                adjacency,
                reanchoredPaths,
                baseView.ActiveByPath);
            equivalent = LeanPropositionSourceComparer.AreEquivalent(
                protectedBase,
                candidate,
                reanchoredPaths,
                baseView,
                candidateCatalog);
            if (!equivalent)
            {
                failureDetail = "Lean proposition source comparer returned false";
            }
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            failureDetail = exception.Message;
        }

        if (!equivalent)
        {
            throw new InvalidOperationException(
                "reanchor requires equivalent Lean proposition source for "
                + string.Join(", ", reanchoredPaths
                    .OrderBy(static path => path.Value, StringComparer.Ordinal)
                    .Select(static path => path.Value))
                + (failureDetail is null ? string.Empty : $": {failureDetail}"));
        }
    }

    private static string ResolveOutputPath(
        string repositoryRoot,
        string atomId,
        string relativeOut)
    {
        if (Path.IsPathRooted(relativeOut))
        {
            throw new InvalidOperationException("receipt --out must be repository-relative");
        }

        var fullRepositoryRoot = Path.GetFullPath(repositoryRoot);
        var outputPath = Path.GetFullPath(Path.Combine(
            fullRepositoryRoot,
            relativeOut.Replace('/', Path.DirectorySeparatorChar)));
        var outputDirectory = Path.GetDirectoryName(outputPath);
        var canonicalDirectory = Path.GetFullPath(Path.Combine(
            fullRepositoryRoot,
            "Meta/Digestion/formalizations"));
        if (!string.Equals(outputDirectory, canonicalDirectory, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                "receipt --out must resolve directly under Meta/Digestion/formalizations/");
        }

        var canonicalFileName = Path.GetFileName(
            DigestionFormalizationReceipt.PathForAtom(atomId));
        var outputFileName = Path.GetFileName(outputPath);
        var temporaryPrefix = canonicalFileName + ".tmp.";
        if (!string.Equals(outputFileName, canonicalFileName, StringComparison.Ordinal)
            && (!outputFileName.StartsWith(temporaryPrefix, StringComparison.Ordinal)
                || outputFileName.Length == temporaryPrefix.Length))
        {
            throw new InvalidOperationException(
                $"receipt --out must name {canonicalFileName} or {temporaryPrefix}<suffix>");
        }

        return outputPath;
    }

    private sealed record ReceiptArguments(
        string AtomId,
        ImmutableArray<string> Gids,
        string? OutPath,
        bool ReanchorSignature,
        string? BaselineRevision);

    private static ReceiptArguments ParseArguments(IReadOnlyList<string> arguments)
    {
        string? atomId = null;
        var gids = ImmutableArray.CreateBuilder<string>();
        string? outPath = null;
        var reanchorSignature = false;
        string? baselineRevision = null;
        var reanchorSyntax = arguments.Contains("--reanchor-signature", StringComparer.Ordinal)
            || arguments.Contains("--base", StringComparer.Ordinal);
        for (var index = 0; index < arguments.Count;)
        {
            if (arguments[index] == "--reanchor-signature")
            {
                if (reanchorSignature)
                {
                    throw Usage(reanchorSyntax);
                }

                reanchorSignature = true;
                index++;
                continue;
            }

            if (index + 1 >= arguments.Count)
            {
                throw Usage(reanchorSyntax);
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
                case "--base" when baselineRevision is null:
                    baselineRevision = arguments[index + 1];
                    break;
                default:
                    throw Usage(reanchorSyntax);
            }

            index += 2;
        }

        if (string.IsNullOrWhiteSpace(atomId)
            || gids.Count == 0
            || gids.Any(string.IsNullOrWhiteSpace)
            || gids.Distinct(StringComparer.Ordinal).Count() != gids.Count
            || reanchorSignature != (baselineRevision is not null)
            || baselineRevision is not null && string.IsNullOrWhiteSpace(baselineRevision))
        {
            throw Usage(reanchorSyntax);
        }

        if (outPath is not null && string.IsNullOrWhiteSpace(outPath))
        {
            throw new InvalidOperationException("receipt --out must not be empty");
        }

        return new ReceiptArguments(
            atomId,
            gids.ToImmutable(),
            outPath,
            reanchorSignature,
            baselineRevision);
    }

    private static InvalidOperationException Usage(bool includeReanchor = false) => new(
        "USAGE: StrataLint emit-formalization-receipt --atom-id ATOM_ID --gid PRIMARY_GID "
        + "[--gid SECONDARY_GID ...] "
        + "[--out RECEIPT_PATH]"
        + (includeReanchor ? " [--reanchor-signature --base REV]" : string.Empty));

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

using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    // Refresh a derived registry field without running residual admission or status alignment.
    // Both modes validate the exact same candidate; apply additionally requires its published hash.
    private static CommandResult RefreshSourceRegistry(
        string root, IRepositoryGateway repository, ILeanReportSource reports,
        IScribeEmissionVerifier scribe, IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count is not (5 or 6) || arguments[0] != "--base"
                || string.IsNullOrWhiteSpace(arguments[1]) || arguments[2] != "--refresh-source"
                || string.IsNullOrWhiteSpace(arguments[3])
                || !(arguments.Count == 5 && arguments[4] == "--plan"
                    || arguments.Count == 6 && arguments[4] == "--apply"
                    && arguments[5].Length == 64 && arguments[5].All(static c => char.IsAsciiHexDigitLower(c))))
                throw new InvalidOperationException(
                    "USAGE: align-digestion-status --base REV --refresh-source EXISTING_ID_OR_PATH --plan|--apply PLAN_SHA256");

            var inputs = ReadInputs(repository, arguments[1]);
            var sources = inputs.CurrentDocument.RequireDigestionSources();
            var matches = sources.Where(source => source.SourceId == arguments[3]
                || source.SourcePath == arguments[3]).ToArray();
            if (matches.Length != 1)
                throw new InvalidOperationException("selector must resolve exactly one existing source");
            var selected = matches[0];
            if (!inputs.Current.TryGetFile(selected.SourcePath, out var sourceFile))
                throw new InvalidOperationException($"source path is dangling: {selected.SourcePath}");
            var atomized = AtomizerRegistry.Atomize(selected.Atomizer, sourceFile.RawBytes.AsSpan(),
                TheoryAtomizerDataLoader.Load(inputs.Current));
            if (DigestionLedgerAligner.AtomizerIntegrityFailure(atomized, sourceFile.RawBytes.AsSpan()) is { } failure)
                throw new InvalidOperationException($"source {selected.SourceId} atomizer integrity failed: {failure}");
            var replacement = inputs.CurrentDocument.WithDigestionSources(sources.Select(source =>
                source.SourceId == selected.SourceId
                    ? source with { GenreRegistryProjection = GenreRegistryProjection.Available(atomized.GenreRegistryCheck) }
                    : source).ToImmutableArray());
            var candidateRaw = ReplaceLedger(inputs.CurrentRaw, inputs.CurrentDocument, replacement);
            var metadataPath = $"{BackfillInventoryLoader.RootPath}{selected.SourceId}/source.toml";
            var writeChanges = EffectiveChanges(inputs.CurrentRaw, candidateRaw);
            if (writeChanges.Entries.Any(change => change.Path.Value != metadataPath
                || change.Kind != RawChangeKind.Modified))
                throw new InvalidOperationException("registry refresh would write outside the selected source metadata");
            var updates = LedgerUpdates(inputs.CurrentRaw, candidateRaw);
            var candidate = Decode(candidateRaw);
            var document = LoadDocument(candidate);
            var report = reports.Load(candidate);
            var lean = ValidateLean(candidate, report);
            var truthStates = LeanTruthStates.Resolve(candidate, lean);
            var changes = EffectiveChanges(inputs.BaselineRaw, candidateRaw);
            var impact = BackfillDeltaImpactResolver.Resolve(candidate, inputs.Baseline, report, document, changes);
            scribe.Verify(candidate, report, impact.ReceiptVerificationChanges);
            var casChanges = DigestionIngestor.IncludeCasReverseDependencies(inputs.BaselineDocument, changes);
            var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
                document, candidate, lean, inputs.BaselineDocument, baselineSnapshot: inputs.Baseline,
                casChanges: casChanges, truthStates: truthStates);
            RequireNoReceiptIntegrityFailure(evaluation);
            var policy = LoadPolicy(candidate);
            var observations = DigestionBackfillValidation.RequireValidBackfill(document, candidate,
                inputs.Baseline, policy, lean, casChanges: casChanges, truthStates: truthStates);

            var beforeByPath = inputs.CurrentRaw.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
            var writes = updates.Select(update => new
            {
                path = update.Path,
                before_sha256 = RegistryHash(beforeByPath[update.Path].Bytes.AsSpan()),
                before_base64 = Convert.ToBase64String(beforeByPath[update.Path].Bytes.AsSpan()),
                after_sha256 = RegistryHash(update.Bytes!.Value.AsSpan()),
                after_base64 = Convert.ToBase64String(update.Bytes!.Value.AsSpan()),
            }).ToArray();
            var binding = new
            {
                schema = "source-registry-refresh-v1",
                source_id = selected.SourceId,
                source_path = selected.SourcePath,
                atomizer = selected.Atomizer,
                baseline_revision = arguments[1],
                input_sha256 = SourceRegistrySnapshotHash(inputs.Current, policy.FileMapSha256),
                baseline_sha256 = SourceRegistrySnapshotHash(inputs.Baseline, policy.FileMapSha256),
                candidate_sha256 = SourceRegistrySnapshotHash(candidate, policy.FileMapSha256),
                lean_report_sha256 = RegistryHash(RawLeanReportArtifact.Write(candidate, report).AsSpan()),
                writes,
            };
            var planHash = RegistryHash(JsonSerializer.SerializeToUtf8Bytes(binding));
            if (arguments[4] == "--apply" && arguments[5] != planHash)
                throw new InvalidOperationException("published plan does not match the current validated inputs and write set");
            if (EffectiveChanges(inputs.CurrentRaw, repository.ReadCurrent()).Entries.Length != 0
                || EffectiveChanges(inputs.BaselineRaw, repository.ReadRevision(arguments[1])).Entries.Length != 0)
                throw new InvalidOperationException("registry refresh inputs changed during validation");
            RequireLedgerUnchanged(root, inputs.CurrentRaw);
            if (arguments[4] == "--apply")
                ApplyLedgerUpdatesAtomically(root, inputs.CurrentRaw, updates,
                    requireInputsUnchanged: RequireInputsUnchanged);
            else
                RequireInputsUnchanged();
            return new CommandResult(true, JsonSerializer.Serialize(new
            {
                plan_hash = planHash,
                applied = arguments[4] == "--apply",
                binding,
                writes,
                validation = new { scope = "FullScan", lean = "accepted", scribe = "accepted",
                    source_backfill = "accepted", observations },
            }) + "\n", string.Empty);

            void RequireInputsUnchanged()
            {
                // Recheck the complete binding at the writer boundary, not only its
                // ledger projection. Read current last, after report and baseline I/O.
                if (RegistryHash(RawLeanReportArtifact.Write(candidate, reports.Load(candidate)).AsSpan())
                        != binding.lean_report_sha256
                    || EffectiveChanges(inputs.BaselineRaw, repository.ReadRevision(arguments[1])).Entries.Length != 0
                    || EffectiveChanges(inputs.CurrentRaw, repository.ReadCurrent()).Entries.Length != 0)
                    throw new InvalidOperationException("registry refresh inputs changed before publication");
            }
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"REGISTRY_REFRESH_INVALID {exception.Message}\n");
        }
    }

    private static string RegistryHash(ReadOnlySpan<byte> bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static string SourceRegistrySnapshotHash(RepositorySnapshot snapshot, string fileMapSha256) =>
        RegistryHash(CanonicalSnapshotWriter.Write(fileMapSha256, snapshot.Files
            .OrderBy(static pair => pair.Key.Value, StringComparer.Ordinal)
            .Select(static pair => SnapshotEntry.FromFile(pair.Key, pair.Value)).ToImmutableArray()).AsSpan());
}

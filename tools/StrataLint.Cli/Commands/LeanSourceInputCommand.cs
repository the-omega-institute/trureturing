using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

// Source consumers own demand. The canonical report preparation loop satisfies these
// requests with current Lean; the admission process only loads the finished sibling.
internal static class LeanSourceInputCommand
{
    internal static ExplicitCommandResult Run(IRepositoryGateway repository, IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count is not (4 or 6) || arguments[0] != "--base" || arguments[2] != "--report"
                || arguments.Count == 6 && arguments[4] != "--context")
                throw new FormatException("USAGE: StrataLint lean-source-input --base REV --report FILE [--context FILE]");
            var current = Decode(repository.ReadCurrent());
            var baseline = Decode(repository.ReadRevision(arguments[1]));
            var contextFile = arguments.Count == 6 ? arguments[5] : arguments[3] + ".source-context.json";
            var input = File.Exists(contextFile)
                ? LeanSourceContextInput.Load(File.ReadAllBytes(contextFile), current, baseline)
                : LeanSourceContextInput.Empty;
            var changes = repository.ReadChanges(arguments[1]);
            foreach (var path in NativeDecideSourceRule.SelectedPaths(current, baseline, changes))
                _ = NativeDecideSourceRule.Inspect(current, path, input);
            var baseView = FrozenLedgerBaseViewReader.Read(baseline);
            if (!baseView.ActiveByPath.IsEmpty && EffectiveLeanPins.TryRead(baseline, out var oldPins)
                && EffectiveLeanPins.TryRead(current, out var newPins) && oldPins != newPins)
            {
                var report = RawLeanReportArtifact.ReadFile(arguments[3], current);
                var truth = DagLedgerCommandPreparation.BuildTruth(current, report);
                var states = LeanTruthStates.Resolve(current, truth.Lean);
                var adjacency = LeanImportAdjacency.Build(current, truth.Lean);
                var catalog = FrozenContentAddress.Build(current, truth.Lean, states, adjacency) switch
                {
                    FrozenMaterialOutcome.Accepted accepted => accepted.Capability,
                    FrozenMaterialOutcome.Rejected rejected => throw new FormatException(rejected.Message),
                    _ => throw new InvalidOperationException("unknown material outcome"),
                };
                var roots = baseView.ActiveByPath.Where(entry => catalog.ByPath.TryGetValue(entry.Key, out var material)
                    && material.StatementId != entry.Value.Material.StatementId).Select(entry => entry.Key).ToImmutableHashSet();
                _ = LeanPropositionSourceComparer.Compare(baseline, current, roots, baseView, catalog, input);
            }
            if (input.MalformedRows.Count > 0)
                throw new FormatException(string.Join("; ", input.MalformedRows));
            var requests = input.Requests.Select(request =>
            {
                var snapshot = request.Side == "current" ? current : baseline;
                var path = RepoPath.CreateKnown(request.Path);
                var file = snapshot.Files[path];
                return new
                {
                    side = request.Side, path = request.Path, kind = request.Kind,
                    module = LeanImportClosure.ModuleName(path), source = file.Text,
                    mode = request.Kind == "registration" ? "source" : request.Side == "current" ? "current" : "projected",
                    sourceSha256 = LeanSourceContextInput.SourceHash(file),
                    producerSha256 = LeanSourceContextInput.ProducerHash(current),
                    configurationSha256 = LeanSourceContextInput.ConfigurationHash(current),
                    graphSha256 = LeanSourceContextInput.GraphHash(snapshot, path),
                    referenceConfigurationSha256 = LeanSourceContextInput.ConfigurationHash(baseline),
                    managed = LeanSourceContextInput.InterfaceSources(snapshot, path).Select(source => new {
                        module = LeanImportClosure.ModuleName(source.Path), path = source.Path.Value, source = source.Text,
                        sourceSha256 = LeanSourceContextInput.SourceHash(source),
                    }).ToArray(),
                    referenceToolchain = baseline.TryGetFile("lean-toolchain", out var toolchain) ? toolchain.Text.Trim() : "",
                    referenceManifest = baseline.TryGetFile("lake-manifest.json", out var manifest) ? manifest.Text : "{}",
                    currentManifest = current.TryGetFile("lake-manifest.json", out var candidateManifest) ? candidateManifest.Text : "{}",
                    currentToolchain = current.TryGetFile("lean-toolchain", out var currentToolchain) ? currentToolchain.Text.Trim() : "",
                };
            }).ToArray();
            return new(0, JsonSerializer.Serialize(new { schema = LeanSourceContextInput.Schema, requests }) + "\n", "");
        }
        catch (Exception exception) when (exception is FormatException or InvalidOperationException
            or ArgumentException or IOException or JsonException)
        { return new(2, "", $"LEAN_SOURCE_INPUT_INVALID {exception.Message}\n"); }
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
    };
}

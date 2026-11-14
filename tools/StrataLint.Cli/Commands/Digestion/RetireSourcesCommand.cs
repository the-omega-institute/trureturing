using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

// Retire a complete intake unit so a subsequent ingest cannot recreate its atoms.
internal static partial class RetireSourcesCommand
{
    private const string TheoryRoot = "docs/develop/theory/";
    private const string ArchiveRoot = "docs/develop/archive/theory/";

    internal static CommandResult Run(string root, IRepositoryGateway repository,
        ILeanReportSource reportSource, IReadOnlyList<string> arguments,
        Action? beforeCommit = null, Action<string, string>? commit = null,
        Action<string>? beforeArchivePublication = null)
    {
        try
        {
            var options = Parse(arguments);
            var metadata = DigestionQuerySelection.ReadSourceMetadata(repository, options.Sources);
            var sources = metadata.Document.RequireDigestionSources();
            foreach (var source in sources)
                if (!source.SourcePath.StartsWith(TheoryRoot, StringComparison.Ordinal)
                    || !source.SourcePath.EndsWith(".md", StringComparison.Ordinal))
                    throw new FormatException($"NOT_THEORY_SOURCE source_id={source.SourceId}");
            var prefixes = sources.Select(source => BackfillInventoryLoader.RootPath + source.SourceId + "/").ToArray();
            var selectedRaw = repository.ReadCurrent(prefixes.Select(prefix => DigestionQuerySelection.Literal(prefix.TrimEnd('/'))).ToArray());
            var loaded = DigestionWorkingTree.Extend(repository,
                DigestionQuerySelection.Load(DigestionQuerySelection.Merge(metadata.Raw, selectedRaw)), Decode,
                sources.Select(source => source.SourcePath).Append("Meta/FILEMAP.toml")
                    .Concat(repository.SearchCurrentPaths([":(glob)Meta/FILEMAP.*.toml"])).ToArray());
            foreach (var source in sources) DigestionSourceEligibility.Require(loaded.Snapshot, source.SourcePath);
            // Deduplicated sources may own no YAML. Resolve their current claims to
            // existing global owners before deciding which evidence is required.
            var claimIds = sources.SelectMany(source => AtomizerRegistry.Require(source.Atomizer)
                    .Atomize(loaded.Raw.Entries.Single(entry => entry.Path == source.SourcePath).Bytes.AsSpan()).Claims)
                .Select(atom => atom.Fingerprints.RawSha256["sha256:".Length..]).Distinct(StringComparer.Ordinal).ToArray();
            loaded = DigestionQuerySelection.ReadChains(repository, DigestionQuerySelection.Load(
                DigestionQuerySelection.Merge(loaded.Raw, DigestionQuerySelection.ReadAtoms(repository, claimIds).Raw)));
            var entries = loaded.Document.RequireDigestionEntries();
            if (entries.GroupBy(entry => entry.AtomId).Any(group => group.Count() != 1))
                throw new FormatException("AMBIGUOUS_ATOM");
            var requiredIds = entries.Select(entry => entry.AtomId).ToHashSet(StringComparer.Ordinal);
            foreach (var entry in entries.Where(entry => entry.Receipts.Nonpropositional is not null))
                loaded = DigestionQuerySelection.Load(DigestionQuerySelection.Merge(loaded.Raw,
                    DigestionQuerySelection.ReadContext(repository, entry.AtomId).Raw));
            var contextIds = loaded.Raw.Entries.Where(entry => DigestionContextPointerStore.IsCanonicalPath(entry.Path))
                .SelectMany(entry => DigestionContextPointerStore.ParseVersions(entry.Bytes,
                    DigestionQuerySelection.SourceId(entry.Path), Path.GetFileNameWithoutExtension(entry.Path)))
                .SelectMany(index => index.Entries).SelectMany(entry => entry.Occurrences)
                .SelectMany(occurrence => occurrence.GoverningContext.Select(scope => scope.AtomId)
                    .Concat(new[] { occurrence.PreviousAtomId, occurrence.NextAtomId }.OfType<string>()))
                .Distinct(StringComparer.Ordinal).ToArray();
            var inputs = loaded.Document.RequireDigestionSources().Select(source => source.SourcePath)
                .Concat(entries.Select(DigestionQuerySelection.CasPath)).Append("Meta/FILEMAP.toml")
                .Concat(contextIds.Select(id => DigestionCasStore.RootPath + id))
                .Concat(repository.SearchCurrentPaths([":(glob)Meta/FILEMAP.*.toml"]))
                .Concat(entries.Any(entry => !entry.Coverage.IsEmpty)
                    ? ["D5", "Reg", "Trureturing.lean", "Golden/Frozen/state"] : Array.Empty<string>())
                .ToArray();
            loaded = DigestionWorkingTree.Extend(repository, loaded, Decode, inputs);
            foreach (var source in sources) DigestionSourceEligibility.Require(loaded.Snapshot, source.SourcePath);
            var targets = entries.SelectMany(entry => entry.CoverageGids)
                .Select(gid => Gid.TryParse(gid, out var parsed) && parsed.ToTarget() is Target.Formal
                    ? parsed.Path : throw new FormatException($"INVALID_COVERAGE gid={gid}"))
                .Distinct().ToArray();
            if (options.LeanInputs)
                return new(true, string.Join(' ', targets.Select(path => path.Value[..^5].Replace('/', '.'))) + "\n", string.Empty);
            RequireTerminal(loaded.Snapshot, loaded.Document, requiredIds,
                sources.Select(source => source.SourceId).ToHashSet(StringComparer.Ordinal), targets, reportSource);

            var removedIds = sources.SelectMany(source => loaded.Document.RequireDigestionSources()
                    .Single(current => current.SourceId == source.SourceId).Entries)
                .Select(entry => entry.AtomId).ToHashSet(StringComparer.Ordinal);
            var archivePaths = options.Mode == "archive"
                ? sources.Select(source => ArchiveRoot + source.SourcePath[TheoryRoot.Length..]).ToArray() : [];
            var captured = RequireNoReferences(repository, loaded.Snapshot, prefixes, removedIds, sources.Select(source => source.SourcePath).ToArray(), archivePaths);
            var updates = ImmutableArray.CreateBuilder<IngestCommand.LedgerUpdate>();
            foreach (var source in sources)
            {
                var original = loaded.Raw.Entries.Single(entry => entry.Path == source.SourcePath);
                if (options.Mode == "archive")
                {
                    var destination = ArchiveRoot + source.SourcePath[TheoryRoot.Length..];
                    if (repository.SearchCurrentPaths([DigestionQuerySelection.Literal(destination)]).Count > 0)
                        throw new FormatException($"ARCHIVE_EXISTS path={destination}");
                    if (FileMapLoader.LoadSnapshot(loaded.Snapshot).Match(destination) is not
                        [{ Kind: FileMapKind.Data, ProducedBy: "none", ConsumedBy: ["reader"],
                            RuntimeDisposition: "committed-source", DigestionSource: false, Symlink: null }])
                        throw new FormatException($"ARCHIVE_POLICY_MISSING path={destination}");
                    updates.Add(new(destination, ArchiveMarkdown(original.Bytes, source.SourcePath, destination,
                        sources.Select(item => item.SourcePath).ToArray()), -1));
                }
                updates.Add(new(source.SourcePath, null));
            }
            foreach (var entry in selectedRaw.Entries.Where(entry => prefixes.Any(prefix => entry.Path.StartsWith(prefix, StringComparison.Ordinal))))
                updates.Add(new(entry.Path, null));
            var output = string.Concat(sources.Select(source =>
                $"RETIRE_SOURCE source_id={source.SourceId} mode={options.Mode} atoms={loaded.Document.RequireDigestionSources().Single(current => current.SourceId == source.SourceId).Entries.Length}\n"));
            if (!options.Write) return new(true, "RETIRE_PREVIEW\n" + output, string.Empty);
            var current = DigestionQuerySelection.Merge(loaded.Raw, captured);
            beforeCommit?.Invoke();
            ApplyRetirementAtomically(root, current, updates.ToImmutable(), commit, beforeArchivePublication, () =>
            {
                var reread = repository.ReadCurrent(current.Entries.Select(entry => DigestionQuerySelection.Literal(entry.Path)).ToArray());
                RequireSame(current, reread);
                var fresh = RequireNoReferences(repository, loaded.Snapshot, prefixes, removedIds, sources.Select(source => source.SourcePath).ToArray(), archivePaths);
                RequireSame(captured, fresh);
                var freshSelected = repository.ReadCurrent(prefixes.Select(prefix => DigestionQuerySelection.Literal(prefix.TrimEnd('/'))).ToArray());
                RequireSame(selectedRaw, freshSelected);
                foreach (var update in updates) RequireRegularPath(root, update.Path);
            });
            return new(true, "RETIRE_WRITTEN\n" + output, string.Empty);
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            return new(false, string.Empty, $"RETIRE_INVALID {error.Message}\n");
        }
    }

    private static void RequireTerminal(RepositorySnapshot snapshot, BackfillInventoryDocument document,
        HashSet<string> requiredIds, HashSet<string> selectedSources, RepoPath[] targets, ILeanReportSource reportSource)
    {
        var contextDocument = document;
        document = document.WithDigestionSources(document.RequireDigestionSources()
            .Select(source => source with { Entries = source.Entries.Where(entry => requiredIds.Contains(entry.AtomId)).ToImmutableArray() })
            .OrderByDescending(source => selectedSources.Contains(source.SourceId)).ToImmutableArray());
        var entries = document.RequireDigestionEntries();
        _ = DigestionDecomposition.ValidatedClosure(entries.Select(entry => entry.AtomId),
            entries.ToDictionary(entry => entry.AtomId, StringComparer.Ordinal), snapshot);
        DigestionLedgerEvaluation evaluation;
        if (targets.Length == 0)
            evaluation = DigestionStatusEvaluator.EvaluateUncovered(DigestionEvaluationScope.FullScan, document, snapshot);
        else
        {
            var report = LeanReportSourceScope.Load(reportSource, snapshot, targets);
            var lean = LeanClosureValidator.Validate(snapshot, report) switch
            {
                LeanValidationOutcome.Accepted accepted => accepted.Capability,
                LeanValidationOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
            };
            evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan, document, snapshot, lean);
        }
        IngestCommand.RequireNoReceiptIntegrityFailure(evaluation);
        if (evaluation.Entries.Length != entries.Length) throw new FormatException("INCOMPLETE_EVALUATION");
        foreach (var item in evaluation.Entries)
        {
            var nonpropositional = item.DerivedStatus == new DigestionStatus(DigestionMigrationState.Nonpropositional, DigestionTruthState.Inapplicable)
                && item.Entry.Receipts.Nonpropositional is { IsValid: true };
            var closed = item.Deletable && item.DerivedStatus == new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed);
            if ((!closed && !nonpropositional) || item.DerivedStatus != item.Entry.ProjectedStatus || !item.Gaps.IsEmpty
                || !item.Entry.Receipts.UnresolvedSubitems.IsEmpty || item.Entry.Receipts.Quarantine is not null
                || item.Entry.Receipts.CoverDisposition is not null || item.Entry.Receipts.TailAuthorization is not null)
                throw new FormatException($"ATOM_NOT_TERMINAL {item.Render()}");
            if (nonpropositional)
            {
                var receipt = item.Entry.Receipts.Nonpropositional!;
                if (!DigestionAtomContextProjection.ResolveOccurrences(snapshot, contextDocument, item.Entry.AtomId).Any(context =>
                        context.Previous?.AtomId == receipt.PreviousAtomId && context.Next?.AtomId == receipt.NextAtomId))
                    throw new FormatException($"CONTEXT_MISMATCH atom_id={item.Entry.AtomId}");
            }
        }
        // Recorded terminal entries must also account for the current source's complete claim set.
        var alignment = DigestionLedgerAligner.Evaluate(document, snapshot, DigestionAlignmentMode.Projection);
        if (alignment.Findings.Length > 0 || alignment.Residual.Any(item => selectedSources.Contains(item.SourceId)))
            throw new FormatException("SOURCE_HAS_RESIDUAL_OR_INVALID_CLAIMS");
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
    };

    private sealed record Options(string[] Sources, string Mode, bool Write, bool LeanInputs);

    private static Options Parse(IReadOnlyList<string> arguments)
    {
        var sources = new List<string>();
        string? mode = null;
        var write = false;
        var leanInputs = false;
        for (var i = 0; i < arguments.Count; i++)
            switch (arguments[i])
            {
                case "--write" when !write: write = true; break;
                case "--lean-inputs" when !leanInputs: leanInputs = true; break;
                case "--source" when i + 1 < arguments.Count: sources.Add(arguments[++i]); break;
                case "--mode" when mode is null && i + 1 < arguments.Count: mode = arguments[++i]; break;
                default: throw Usage();
            }
        if (sources.Count == 0 || mode is not ("archive" or "delete") || write && leanInputs) throw Usage();
        return new(sources.Distinct(StringComparer.Ordinal).ToArray(), mode, write, leanInputs);
    }

    private static FormatException Usage() => new(
        "USAGE: StrataLint retire-sources --source SOURCE_ID_OR_PATH [--source ...] --mode archive|delete [--write | --lean-inputs]");
}

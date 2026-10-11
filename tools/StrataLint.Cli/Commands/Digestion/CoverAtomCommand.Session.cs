using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverAtomCommand
{
    internal sealed class Session
    {
        private readonly string root;
        private RepositorySnapshot? current;
        private BackfillInventoryDocument? document;
        internal RawRepositorySnapshot CurrentRaw { get; private set; }
        internal RepositorySnapshot Current => current ??= Decode(CurrentRaw);
        // The ledger as the session first read it: the state its writes are compared with.
        internal RepositorySnapshot Baseline { get; }
        internal BackfillInventoryDocument Document => document ??= LoadDocument(Current);
        internal LeanAxiomReport Report { get; }
        internal AcceptedLeanClosure Lean { get; }
        internal FrozenStateCatalog FrozenState { get; }
        internal FrozenStatementIndex FrozenStatements { get; }
        internal IReadOnlyDictionary<RepoPath, TruthState> TruthStates { get; }
        internal RawChangeSet Changes { get; private set; }
        internal bool Invalidated { get; private set; }

        internal Session(string root, IRepositoryGateway repository, ILeanReportSource reportSource,
            DateTimeOffset recordedAtUtc, string firstGid, IReadOnlyList<string> atomIds,
            IReadOnlyCollection<RepoPath>? reportTargets = null)
        {
            this.root = root;
            (CurrentRaw, current, document) = ReadInputs(repository, atomIds);
            Baseline = current;
            IReadOnlyCollection<RepoPath> roots;
            if (reportTargets is { Count: > 0 })
            {
                roots = reportTargets;
            }
            else if (Gid.TryParse(firstGid, out var first))
            {
                roots = [first.Path];
            }
            else
            {
                throw new InvalidOperationException($"cover report target is not a GID: {firstGid}");
            }
            roots = ReportTargets(Document, roots);
            Report = LeanReportSourceScope.Load(reportSource, Current, roots);
            Lean = ValidateLean(Current, Report);
            try
            {
                FrozenState = FrozenStateCatalog.Load(Current);
            }
            catch (Exception exception) when (exception is FormatException or InvalidOperationException)
            {
                var target = Gid.TryParse(firstGid, out var gid) ? gid.Path.Value : firstGid;
                throw new InvalidOperationException(
                    $"cover target module {target} is not frozen; run make deposit before cover");
            }
            ValidateExistingCoveragePins();
            FrozenStatements = FrozenStatementIndex.Create(FrozenState, Report);
            TruthStates = LeanTruthStates.Resolve(Current, Lean);
            Changes = RawChangeSet.Create([]);
        }

        internal static CommandResult LeanInputs(IRepositoryGateway repository, IReadOnlyList<string> atomIds,
            IReadOnlyCollection<RepoPath> requested)
        {
            var inputs = ReadInputs(repository, atomIds);
            foreach (var atomId in atomIds)
                if (inputs.Document.RequireDigestionEntries().Count(entry => entry.AtomId == atomId) != 1)
                    throw new InvalidOperationException($"cover atom {atomId} is absent or ambiguous in the ledger");
            var targets = ReportTargets(inputs.Document, requested);
            _ = LeanReportScope.Create(inputs.Snapshot, targets);
            return new CommandResult(true,
                string.Join(' ', targets.Select(static path => path.Value[..^5].Replace('/', '.'))) + "\n", string.Empty);
        }

        private static RepoPath[] ReportTargets(BackfillInventoryDocument document, IEnumerable<RepoPath> requested) =>
            requested.Concat(document.RequireDigestionEntries().SelectMany(static entry => entry.CoverageGids)
                .Select(gid => Gid.TryParse(gid, out var parsed) && parsed.ToTarget() is Target.Formal
                    ? parsed.Path
                    : throw new InvalidOperationException($"existing coverage GID is not a formal target: {gid}")))
                .Distinct().OrderBy(static path => path.Value, StringComparer.Ordinal).ToArray();

        private void ValidateExistingCoveragePins()
        {
            var recorded = FrozenLedgerBaseViewReader.Read(Current);
            foreach (var path in ReportTargets(Document, []))
            {
                if (!FrozenState.Records.TryGetValue(path, out var pin)
                    || !recorded.ActiveByPath.TryGetValue(path, out var active)
                    || pin.StatementId != active.Material.StatementId)
                    throw new InvalidOperationException($"existing coverage target has no consistent frozen pin: {path.Value}");
                if (!Report.Files.TryGetValue(path, out var module)
                    || !active.Material.DeclarationStatementIds.SequenceEqual(
                        CanonicalStatementWriter.DeclarationStatementIds(path, module)))
                    throw new InvalidOperationException($"coverage-target-mismatch: {path.Value}; current declarations differ from the frozen target");
            }
        }

        private static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document)
            ReadInputs(IRepositoryGateway repository, IReadOnlyList<string> atomIds)
        {
            var selected = DigestionQuerySelection.ReadAtoms(repository, atomIds);
            var visited = atomIds.ToHashSet(StringComparer.Ordinal);
            var pending = selected.Document.RequireDigestionEntries()
                .SelectMany(static entry => entry.Receipts.ChainAtoms).ToArray();
            var casPaths = selected.Document.RequireDigestionEntries()
                .Where(static entry => !entry.Receipts.ChainAtoms.IsEmpty)
                .Where(static entry => DigestionFingerprint.IsCanonicalSha256(entry.CasRef))
                .Select(DigestionQuerySelection.CasPath).ToHashSet(StringComparer.Ordinal);
            while (pending.Length > 0)
            {
                var referencedIds = pending.ToHashSet(StringComparer.Ordinal);
                foreach (var entry in selected.Document.RequireDigestionEntries()
                    .Where(entry => referencedIds.Contains(entry.AtomId)
                        && DigestionFingerprint.IsCanonicalSha256(entry.CasRef)))
                    casPaths.Add(DigestionQuerySelection.CasPath(entry));
                var frontier = pending.Where(visited.Add)
                    .Where(static id => DigestionFingerprint.IsCanonicalSha256("sha256:" + id)).ToArray();
                if (frontier.Length == 0) break;
                var referenced = DigestionQuerySelection.ReadAtoms(repository, frontier);
                if (!referenced.Raw.Entries.IsEmpty)
                    selected = DigestionQuerySelection.Load(DigestionQuerySelection.Merge(selected.Raw, referenced.Raw));
                var ids = frontier.ToHashSet(StringComparer.Ordinal);
                var entries = selected.Document.RequireDigestionEntries().Where(entry => ids.Contains(entry.AtomId)).ToArray();
                foreach (var entry in entries.Where(static entry => DigestionFingerprint.IsCanonicalSha256(entry.CasRef)))
                    casPaths.Add(DigestionQuerySelection.CasPath(entry));
                pending = entries.SelectMany(static entry => entry.Receipts.ChainAtoms).ToArray();
            }

            var declared = selected.Document.RequireDigestionSources()
                .SelectMany(static source => source.Entries
                    .SelectMany(static entry => entry.CoverageGids
                        .Select(static gid => Gid.TryParse(gid, out var parsed) ? parsed.Path.Value : null)
                        .Append(entry.Receipts.TailAuthorization?.Path))
                    .Append(source.SourcePath))
                .OfType<string>().Where(static path => RepoPath.TryCreate(path, out _));
            var paths = new[]
                {
                    TheoryAtomizerDataLoader.DataPath, "D5", "Reg", "Trureturing.lean", "Golden/Frozen/state",
                    FrozenLedgerChangeClassifier.AcceptedRoot,
                }
                .Concat(declared.Select(DigestionQuerySelection.Literal))
                .Concat(casPaths.Select(DigestionQuerySelection.Literal))
                .Distinct(StringComparer.Ordinal).ToArray();
            var raw = DigestionQuerySelection.Merge(selected.Raw, repository.ReadCurrent(paths));
            return (raw, Decode(raw), selected.Document);
        }

        internal CommandResult Apply(string atomId, ImmutableArray<string> gids) =>
            CoverAtomCommand.Apply(this, new CoverArguments(atomId, gids), allowAlreadyApplied: true);

        internal void Commit(RawRepositorySnapshot raw, ImmutableArray<IngestCommand.LedgerUpdate> updates)
        {
            try
            {
                IngestCommand.ApplyLedgerUpdatesAtomically(root, CurrentRaw, updates);
            }
            catch
            {
                Invalidated = true;
                throw;
            }

            // Include our own directory migrations in subsequent delta evaluations.
            var changes = Changes.Entries.ToDictionary(change => change.Path.Value, change => change.Kind,
                StringComparer.Ordinal);
            foreach (var update in updates)
            {
                var atBase = Baseline.TryGetFile(update.Path, out var baselineFile);
                if (update.Bytes is null && !atBase
                    || update.Bytes is { } bytes && atBase
                    && bytes.AsSpan().SequenceEqual(baselineFile!.RawBytes.AsSpan()))
                {
                    changes.Remove(update.Path);
                }
                else
                {
                    changes[update.Path] = update.Bytes is null ? RawChangeKind.Deleted
                        : atBase ? RawChangeKind.Modified : RawChangeKind.Added;
                }
            }
            Changes = RawChangeSet.CreateWithKinds(changes.Select(pair => (pair.Key, pair.Value)));
            CurrentRaw = raw;
            current = null;
            document = null;
        }
    }
}

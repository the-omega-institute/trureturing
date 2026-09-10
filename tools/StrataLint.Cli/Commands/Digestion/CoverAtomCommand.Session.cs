using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverAtomCommand
{
    internal sealed class Session
    {
        private readonly string root;
        private readonly string baselineRevision;
        internal RawRepositorySnapshot CurrentRaw { get; private set; }
        internal RepositorySnapshot Current { get; private set; }
        internal RepositorySnapshot Baseline { get; }
        internal BackfillInventoryDocument Document { get; private set; }
        internal BackfillInventoryDocument BaselineDocument { get; }
        internal LeanAxiomReport Report { get; }
        internal AcceptedLeanClosure Lean { get; }
        internal FrozenStateCatalog FrozenState { get; }
        internal FrozenStatementIndex FrozenStatements { get; }
        internal IReadOnlyDictionary<RepoPath, TruthState> TruthStates { get; }
        internal ValidatedPolicy Policy { get; }
        internal IScribeEmissionVerifier Scribe { get; }
        internal RawChangeSet Changes { get; private set; }
        internal Action? ValidateInputs { get; set; }
        internal bool Invalidated { get; private set; }

        internal Session(string root, IRepositoryGateway repository, ILeanReportSource reportSource,
            IScribeEmissionVerifier scribe, DateTimeOffset recordedAtUtc, string baselineRevision, string firstGid)
        {
            this.root = root;
            this.baselineRevision = baselineRevision;
            Scribe = scribe;
            CurrentRaw = repository.ReadCurrent();
            Current = Decode(CurrentRaw);
            Baseline = Decode(repository.ReadRevision(baselineRevision));
            Document = LoadDocument(Current);
            BaselineDocument = IngestCommand.LoadDocument(Baseline, baseline: true);
            Report = reportSource.Load(Current);
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
            FrozenStatements = FrozenStatementIndex.Create(FrozenState, Report);
            TruthStates = LeanTruthStates.Resolve(Current, Lean);
            Policy = LoadPolicy(Current);
            Changes = repository.ReadChanges(baselineRevision);
        }

        internal CommandResult Apply(string atomId, ImmutableArray<string> gids) =>
            CoverAtomCommand.Apply(this, new CoverArguments(atomId, gids, baselineRevision), allowAlreadyApplied: true);

        internal void RequireUnchanged()
        {
            try
            {
                ValidateInputs?.Invoke();
                IngestCommand.RequireLedgerUnchanged(root, CurrentRaw);
            }
            catch
            {
                Invalidated = true;
                throw;
            }
        }

        internal void Commit(RawRepositorySnapshot raw, RepositorySnapshot snapshot,
            BackfillInventoryDocument document, ImmutableArray<IngestCommand.LedgerUpdate> updates)
        {
            try
            {
                ValidateInputs?.Invoke();
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
            Current = snapshot;
            Document = document;
        }
    }
}

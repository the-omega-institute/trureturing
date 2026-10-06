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
            DateTimeOffset recordedAtUtc, string firstGid)
        {
            this.root = root;
            (CurrentRaw, current, document) = DigestionWorkingTree.Read(repository, Decode, LoadDocument);
            Baseline = current;
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
            Changes = RawChangeSet.Create([]);
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

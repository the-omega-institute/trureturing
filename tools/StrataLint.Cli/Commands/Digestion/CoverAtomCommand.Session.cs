using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverAtomCommand
{
    internal sealed class Session
    {
        // Every cover reads these families: the ledger with its CAS, atomizer and
        // registry documents, the Lean sources the report is bound to, and the
        // frozen state. The ledger names the rest: source documents, non-Lean
        // coverage targets, tail authorizations and the registered build inputs.
        private static readonly string[] Scope =
            ["Meta", "D5", "Reg", "Trureturing.lean", "Golden/Frozen/state"];

        private readonly string root;
        private RepositorySnapshot? current;
        private BackfillInventoryDocument? document;
        internal RawRepositorySnapshot CurrentRaw { get; private set; }
        internal RepositorySnapshot Current => current ??= Decode(CurrentRaw);
        // The ledger as the session first read it: the state its writes are compared with.
        internal RepositorySnapshot Baseline { get; }
        internal BackfillInventoryDocument Document => document ??= LoadDocument(Current);
        internal BackfillInventoryDocument BaselineDocument { get; }
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
            var scopedRaw = repository.ReadCurrent(Scope);
            var scoped = Decode(scopedRaw);
            document = LoadDocument(scoped);
            var declared = Outside(Scope, DeclaredPaths(document).Concat(RegisteredBuildInputs(scoped)));
            CurrentRaw = declared.Length == 0
                ? scopedRaw
                : Merge(scopedRaw, repository.ReadCurrent(
                    [.. declared.Select(static path => ":(literal)" + path)]));
            current = declared.Length == 0 ? scoped : Decode(CurrentRaw);
            Baseline = current;
            BaselineDocument = document;
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

        private static IEnumerable<string> DeclaredPaths(BackfillInventoryDocument document) =>
            document.RequireDigestionSources().SelectMany(static source => source.Entries
                .SelectMany(static entry => entry.CoverageGids
                    .Select(static gid => Gid.TryParse(gid, out var parsed) ? parsed.Path.Value : null)
                    .Append(entry.Receipts.TailAuthorization?.Path))
                .Append(source.SourcePath))
            .OfType<string>();

        private static string[] RegisteredBuildInputs(RepositorySnapshot snapshot) =>
            snapshot.TryGetFile(EngineeringProjectRegistry.ManifestPath, out var manifest)
                ? EngineeringProjectRegistry.Parse(manifest.Text).RuleBuildInputs
                : [];

        private static string[] Outside(string[] scope, IEnumerable<string> paths) =>
            paths.Where(path => RepoPath.TryCreate(path, out _)
                    && !scope.Any(root => path == root || path.StartsWith(root + "/", StringComparison.Ordinal)))
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToArray();

        private static RawRepositorySnapshot Merge(RawRepositorySnapshot scoped, RawRepositorySnapshot extra) =>
            RawRepositorySnapshot.Create(scoped.Entries.Concat(extra.Entries)
                .DistinctBy(static entry => entry.Path, StringComparer.Ordinal)
                .OrderBy(static entry => entry.Path, StringComparer.Ordinal));

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

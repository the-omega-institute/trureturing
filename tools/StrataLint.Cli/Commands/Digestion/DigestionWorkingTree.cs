using StrataLint.Engine;

namespace StrataLint.Cli;

// What a digestion command reads from the working tree. Evaluation commands
// consume the complete governance scope and the ledger-declared inputs; query
// and report-free mutation commands select only the ledger, atomizer data, and
// explicitly requested source or CAS paths.
internal static class DigestionWorkingTree
{
    // Evaluation reads the ledger and the files named by the entries it is
    // actually evaluating.  CAS blobs are fetched only by commands that need
    // a particular atom; a status query must not expand the entire CAS tree.
    private static readonly string[] EvaluationScope =
        [
            BackfillInventoryLoader.RelativePath,
            BackfillInventoryLoader.RootPath.TrimEnd('/'),
            TheoryAtomizerDataLoader.DataPath,
            "D5",
            "Reg",
            "Trureturing.lean",
            "Golden/Frozen/state",
        ];

    // Query and report-free mutation commands do not consume Lean, frozen-state,
    // registry, or the complete CAS tree. Keep those facts out of their input
    // snapshot so their behavior follows the facts they actually inspect.
    private static readonly string[] LedgerScope =
        [
            BackfillInventoryLoader.RootPath.TrimEnd('/'),
            BackfillInventoryLoader.RelativePath,
        ];

    private static readonly string[] IngestScope =
        [
            BackfillInventoryLoader.RootPath.TrimEnd('/'),
            BackfillInventoryLoader.RelativePath,
            TheoryAtomizerDataLoader.DataPath,
        ];

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadEvaluation(
        IRepositoryGateway repository,
        Func<RawRepositorySnapshot, RepositorySnapshot> decode,
        Func<RepositorySnapshot, BackfillInventoryDocument> load,
        params string[] additional)
    {
        var scoped = ReadScoped(repository, decode, load, EvaluationScope,
            includeDeclared: true, additional: additional);
        var chainRoots = scoped.Document.RequireDigestionEntries()
            .Where(static entry => !entry.Receipts.ChainAtoms.IsEmpty)
            .Select(static entry => entry.AtomId);
        return Extend(repository, scoped.Raw, decode, load, ChainCasPaths(scoped.Document, chainRoots));
    }

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadLedger(
        IRepositoryGateway repository,
        Func<RawRepositorySnapshot, RepositorySnapshot> decode,
        Func<RepositorySnapshot, BackfillInventoryDocument> load,
        params string[] additional)
        => ReadScoped(repository, decode, load, LedgerScope, includeDeclared: false, additional: additional);

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadIngest(
        IRepositoryGateway repository,
        Func<RawRepositorySnapshot, RepositorySnapshot> decode,
        Func<RepositorySnapshot, BackfillInventoryDocument> load,
        params string[] additional)
    {
        // Report-free ingestion and source-registry refresh only atomize source
        // bytes and append/update their own ledger records.  Coverage targets,
        // tail artifacts, and rule build inputs belong to evaluation/admission;
        // reading them here only couples a local mutation to unrelated systems.
        var scoped = ReadScoped(repository, decode, load, IngestScope,
            includeDeclared: false, additional: additional);
        var sourcePaths = scoped.Document.RequireDigestionSources()
            .Select(static source => source.SourcePath);
        return Extend(repository, scoped.Raw, decode, load, sourcePaths.ToArray());
    }

    // Report-free candidate projection only needs the ledger, atomizer inputs,
    // source bytes, and the CAS objects named by that ledger. It must not pull
    // Lean, frozen state, or registry inputs into a query whose result excludes
    // covered entries by design.
    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadUncovered(
        IRepositoryGateway repository,
        RawRepositorySnapshot ledgerRaw,
        Func<RawRepositorySnapshot, RepositorySnapshot> decode,
        Func<RepositorySnapshot, BackfillInventoryDocument> load)
    {
        ArgumentNullException.ThrowIfNull(ledgerRaw);
        var ledgerSnapshot = decode(ledgerRaw);
        var ledger = load(ledgerSnapshot);
        var sourcePaths = ledger.RequireDigestionSources()
            .Select(static source => source.SourcePath);
        var chainRoots = ledger.RequireDigestionEntries()
            .Where(static entry => !entry.Receipts.ChainAtoms.IsEmpty)
            .Select(static entry => entry.AtomId);
        return Extend(
            repository,
            ledgerRaw,
            decode,
            load,
            [
                .. sourcePaths,
                TheoryAtomizerDataLoader.DataPath,
                .. ChainCasPaths(ledger, chainRoots),
            ]);
    }

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) Extend(
        IRepositoryGateway repository,
        RawRepositorySnapshot current,
        Func<RawRepositorySnapshot, RepositorySnapshot> decode,
        Func<RepositorySnapshot, BackfillInventoryDocument> load,
        params string[] additional)
    {
        ArgumentNullException.ThrowIfNull(current);
        var present = current.Entries
            .Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var missing = additional
            .Where(path => !present.Contains(path))
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        if (missing.Length == 0)
        {
            var snapshot = decode(current);
            return (current, snapshot, load(snapshot));
        }

        var extra = repository.ReadCurrent(missing);
        var merged = RawRepositorySnapshot.Create(current.Entries
            .Concat(extra.Entries)
            .DistinctBy(static entry => entry.Path, StringComparer.Ordinal)
            .OrderBy(static entry => entry.Path, StringComparer.Ordinal));
        var decoded = decode(merged);
        return (merged, decoded, load(decoded));
    }

    // A source context only needs CAS objects reachable through persisted chains.
    // Leaf atoms are reconstructed from the source atomizer and do not need their
    // duplicated CAS bytes in the query snapshot.
    internal static string[] ChainCasPaths(
        BackfillInventoryDocument document,
        IEnumerable<string> roots)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(roots);
        // Keep malformed duplicate identities in the ledger for the command's
        // domain validation.  They must not escape as a generic Dictionary
        // exception before the caller can report the expected occurrence error.
        var entries = document.RequireDigestionEntries()
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Where(static group => group.Count() == 1)
            .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);
        var ids = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Queue<string>(roots);
        while (pending.TryDequeue(out var id))
        {
            if (!DigestionNonpropositional.IsAtomId(id) || !ids.Add(id)) continue;
            if (!entries.TryGetValue(id, out var entry)) continue;
            foreach (var childId in entry.Receipts.ChainAtoms)
                pending.Enqueue(childId);
        }

        return ids
            .Select(static id => DigestionCasStore.RootPath + id)
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    private static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadScoped(
        IRepositoryGateway repository,
        Func<RawRepositorySnapshot, RepositorySnapshot> decode,
        Func<RepositorySnapshot, BackfillInventoryDocument> load,
        IReadOnlyList<string> scope,
        bool includeDeclared,
        IReadOnlyList<string> additional)
    {
        var scopedRaw = repository.ReadCurrent([.. scope, .. additional]);
        var scoped = decode(scopedRaw);
        var document = load(scoped);
        if (!includeDeclared)
        {
            return (scopedRaw, scoped, document);
        }

        var declared = DeclaredPaths(document)
            .Where(path => RepoPath.TryCreate(path, out _)
                && !scope.Any(root => path == root || path.StartsWith(root + "/", StringComparison.Ordinal)))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (declared.Length == 0)
        {
            return (scopedRaw, scoped, document);
        }

        var raw = RawRepositorySnapshot.Create(scopedRaw.Entries.Concat(repository.ReadCurrent(declared).Entries)
            .DistinctBy(static entry => entry.Path, StringComparer.Ordinal)
            .OrderBy(static entry => entry.Path, StringComparer.Ordinal));
        return (raw, decode(raw), document);
    }

    private static IEnumerable<string> DeclaredPaths(BackfillInventoryDocument document) =>
        document.RequireDigestionSources().SelectMany(static source => source.Entries
            .SelectMany(static entry => entry.CoverageGids
                .Select(static gid => Gid.TryParse(gid, out var parsed) ? parsed.Path.Value : null)
                .Append(entry.Receipts.TailAuthorization?.Path))
            .Append(source.SourcePath))
        .OfType<string>();

}

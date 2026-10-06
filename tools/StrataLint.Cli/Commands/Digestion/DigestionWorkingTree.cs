using StrataLint.Engine;

namespace StrataLint.Cli;

// What a digestion command reads from the working tree. Every command reads
// these families: the ledger with its CAS, atomizer and registry documents, the
// Lean sources the report is bound to, and the frozen state. The ledger names
// the rest: source documents, non-Lean coverage targets, tail authorizations
// and the registered build inputs.
internal static class DigestionWorkingTree
{
    private static readonly string[] Scope =
        ["Meta", "D5", "Reg", "Trureturing.lean", "Golden/Frozen/state"];

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) Read(
        IRepositoryGateway repository,
        Func<RawRepositorySnapshot, RepositorySnapshot> decode,
        Func<RepositorySnapshot, BackfillInventoryDocument> load,
        params string[] additional)
    {
        var scopedRaw = repository.ReadCurrent([.. Scope, .. additional]);
        var scoped = decode(scopedRaw);
        var document = load(scoped);
        var declared = DeclaredPaths(document).Concat(RegisteredBuildInputs(scoped))
            .Where(static path => RepoPath.TryCreate(path, out _)
                && !Scope.Any(root => path == root || path.StartsWith(root + "/", StringComparison.Ordinal)))
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

    // A command that consumes the registry reports its defects itself.
    private static string[] RegisteredBuildInputs(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile(EngineeringProjectRegistry.ManifestPath, out var manifest))
        {
            return [];
        }

        try
        {
            return EngineeringProjectRegistry.Parse(manifest.Text).RuleBuildInputs;
        }
        catch (InvalidDataException)
        {
            return [];
        }
    }
}

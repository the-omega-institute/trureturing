using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class DigestionQuerySelection
{
    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadContext(
        IRepositoryGateway repository, string atomId, IReadOnlyList<string>? selectors = null)
        => ReadContext(repository, atomId, selectors, out _);

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadContext(
        IRepositoryGateway repository, string atomId, IReadOnlyList<string>? selectors, out AtomizedTheoryDocument? sourceDocument)
    {
        sourceDocument = null;
        var loaded = ReadAtom(repository, atomId, selectors);
        var targets = loaded.Document.RequireDigestionEntries().Where(entry => entry.AtomId == atomId).ToArray();
        if (targets.Length != 1) return loaded;
        var target = targets[0];
        loaded = Load(Merge(loaded.Raw, repository.ReadCurrent([Literal(target.SourcePath), Literal(TheoryAtomizerDataLoader.DataPath)])));
        if (!loaded.Snapshot.TryGetFile(target.SourcePath, out var sourceFile))
            throw new DigestionAtomContextException(DigestionAtomContextError.SOURCE_MISSING,
                $"source_id={target.SourceId} source_path={target.SourcePath}");
        if (target.Atomizer == AtomizerRegistry.NoAtomizerId)
            throw new DigestionAtomContextException(DigestionAtomContextError.ATOMIZER_NONE, $"source_id={target.SourceId}");
        var atomized = AtomizerRegistry.Require(target.Atomizer).Atomize(sourceFile.RawBytes.AsSpan(),
            TheoryAtomizerDataLoader.Load(loaded.Snapshot));
        sourceDocument = atomized;
        var sourceRoot = BackfillInventoryLoader.RootPath + target.SourceId + "/";
        var raw = loaded.Raw;
        var targetSpan = atomized.Claims.Concat(atomized.ClausePlans.SelectMany(static plan => plan.Children))
            .FirstOrDefault(atom => atom.Fingerprints.RawSha256 == target.Fingerprints.RawSha256);
        var targetBytes = targetSpan?.RawBytes;
        if (targetBytes is null)
        {
            var casPath = CasPath(target);
            var cas = repository.ReadCurrent([casPath]);
            raw = Merge(raw, cas);
            var blob = cas.Entries.SingleOrDefault(entry => entry.Path == casPath)
                ?? throw new FormatException($"CAS_MISSING atom_id={atomId}");
            targetBytes = blob.Bytes;
        }

        var neighborIds = new HashSet<string>(StringComparer.Ordinal);
        for (var index = 0; index < atomized.Claims.Length; index++)
        {
            if (atomized.Claims[index].RawBytes.AsSpan().IndexOf(targetBytes.Value.AsSpan()) < 0) continue;
            for (var neighbor = Math.Max(0, index - 1); neighbor <= Math.Min(atomized.Claims.Length - 1, index + 1); neighbor++)
                neighborIds.Add(atomized.Claims[neighbor].Fingerprints.RawSha256[7..]);
        }
        if (neighborIds.Count > 0)
        {
            var paths = repository.SearchCurrentPaths([Literal(sourceRoot.TrimEnd('/'))])
                .Where(IsAtomPath).Where(path => neighborIds.Contains(Path.GetFileNameWithoutExtension(path)))
                .Select(Literal).ToArray();
            var records = paths.Length > 0 ? repository.ReadCurrent(paths) : RawRepositorySnapshot.Create([]);
            raw = Merge(raw, records);
        }
        var local = Load(raw);
        return ReadChains(repository, local);
    }
}

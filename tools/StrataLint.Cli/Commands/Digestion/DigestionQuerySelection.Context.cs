using StrataLint.Engine;
using System.Text;

namespace StrataLint.Cli;

internal static partial class DigestionQuerySelection
{
    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadContext(
        IRepositoryGateway repository, string atomId, IReadOnlyList<string>? selectors = null, bool allowMissing = false)
        => ReadContext(repository, atomId, selectors, out _, allowMissing);

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadContext(
        IRepositoryGateway repository, string atomId, IReadOnlyList<string>? selectors, out AtomizedTheoryDocument? sourceDocument,
        bool allowMissing = false)
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
        var raw = loaded.Raw;
        var targetSpan = atomized.Claims.Concat(atomized.ClausePlans.SelectMany(static plan => plan.Children))
            .FirstOrDefault(atom => atom.Fingerprints.RawSha256 == target.Fingerprints.RawSha256);
        var targetBytes = targetSpan?.RawBytes;
        if (targetBytes is null)
        {
            var casPath = CasPath(target);
            var cas = repository.ReadCurrent([casPath]);
            raw = Merge(raw, cas);
            var blob = cas.Entries.SingleOrDefault(entry => entry.Path == casPath);
            if (blob is null && allowMissing) return Load(raw);
            if (blob is null) throw new FormatException($"CAS_MISSING atom_id={atomId}");
            targetBytes = blob.Bytes;
        }

        var neighborIds = new HashSet<string>(StringComparer.Ordinal);
        for (var index = 0; index < atomized.Claims.Length; index++)
        {
            if (atomized.Claims[index].RawBytes.AsSpan().IndexOf(targetBytes.Value.AsSpan()) < 0) continue;
            for (var neighbor = Math.Max(0, index - 1); neighbor <= Math.Min(atomized.Claims.Length - 1, index + 1); neighbor++)
                neighborIds.Add(atomized.Claims[neighbor].Fingerprints.RawSha256[7..]);
        }
        // Physical AST leaves locate old row/paragraph identities without regenerating
        // historical decomposition. Only their immediate neighborhoods are selected.
        var text = Encoding.UTF8.GetString(sourceFile.RawBytes.AsSpan());
        var leaves = MarkdigBlockAst.Parse(text);
        foreach (var occurrence in DigestionAtomContextProjection.OccurrenceStarts(sourceFile.RawBytes, targetBytes.Value))
        {
            for (var index = 0; index < leaves.Length; index++)
            {
                var start = MarkdownAstAtomizer.ByteOffset(text, leaves[index].Start);
                var end = MarkdownAstAtomizer.ByteOffset(text, leaves[index].End);
                if (start >= occurrence + targetBytes.Value.Length || end <= occurrence) continue;
                for (var neighbor = Math.Max(0, index - 1); neighbor <= Math.Min(leaves.Length - 1, index + 1); neighbor++)
                {
                    start = MarkdownAstAtomizer.ByteOffset(text, leaves[neighbor].Start);
                    end = MarkdownAstAtomizer.ByteOffset(text, leaves[neighbor].End);
                    neighborIds.Add(DigestionFingerprint.Compute(sourceFile.RawBytes.AsSpan()[start..end]).RawSha256[7..]);
                }
            }
        }
        if (neighborIds.Count > 0)
        {
            var neighbors = ReadAtoms(repository, neighborIds.ToArray(), [target.SourceId]);
            raw = Merge(raw, neighbors.Raw);
            var localIds = neighbors.Document.RequireDigestionEntries().Select(static entry => entry.AtomId)
                .ToHashSet(StringComparer.Ordinal);
            var missing = neighborIds.Where(id => !localIds.Contains(id)).ToArray();
            if (missing.Length > 0) raw = Merge(raw, ReadAtoms(repository, missing).Raw);
        }
        var local = Load(raw);
        raw = Merge(raw, repository.ReadCurrent(local.Document.RequireDigestionEntries()
            .Select(CasPath).Distinct(StringComparer.Ordinal).ToArray()));
        local = Load(raw);
        return ReadChains(repository, local, allowMissing: allowMissing);
    }
}

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
        loaded = Load(Merge(loaded.Raw, repository.ReadCurrent([Literal(target.SourcePath), Literal(FileMapLoader.RelativePath), ":(glob)Meta/FILEMAP.*.toml"])));
        if (!loaded.Snapshot.TryGetFile(target.SourcePath, out var sourceFile))
            throw new DigestionAtomContextException(DigestionAtomContextError.SOURCE_MISSING,
                $"source_id={target.SourceId} source_path={target.SourcePath}");
        DigestionSourceEligibility.Require(loaded.Snapshot, target.SourcePath);
        if (!AtomizerRegistry.IsRegistered(target.Atomizer))
            throw new DigestionAtomContextException(DigestionAtomContextError.ATOMIZER_UNSUPPORTED,
                $"source_id={target.SourceId} atomizer={target.Atomizer}");
        var atomized = AtomizerRegistry.Require(target.Atomizer).Atomize(sourceFile.RawBytes.AsSpan());
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
        // Historical cuts need not be fresh claim or physical-leaf boundaries.
        // Catalogue this source's identities, inspect their immutable spans, and
        // retain containing roots and the exterior neighborhood. ReadChains follows
        // their global references regardless of each descendant's source owner.
        var candidateIds = repository.SearchCurrentPaths([Literal(BackfillInventoryLoader.RootPath + target.SourceId)])
            .Where(IsAtomPath).Select(Path.GetFileNameWithoutExtension).OfType<string>()
            .Where(id => DigestionFingerprint.IsCanonicalSha256("sha256:" + id)).Distinct(StringComparer.Ordinal).ToArray();
        var candidatePaths = candidateIds.Select(id => Literal(DigestionCasStore.RootPath + id)).ToArray();
        var existingPaths = repository.SearchCurrentPaths(candidatePaths);
        var candidates = existingPaths.Count == 0 ? RawRepositorySnapshot.Create([])
            : repository.ReadCurrent(existingPaths.Select(Literal).ToArray());
        var historicalIds = DigestionAtomContextProjection.HistoricalNeighborIds(sourceFile.RawBytes,
            targetBytes.Value, candidates.Entries.Select(entry =>
                (Path.GetFileName(entry.Path), entry.Bytes)));
        neighborIds.UnionWith(historicalIds);
        raw = Merge(raw, RawRepositorySnapshot.Create(candidates.Entries
            .Where(entry => historicalIds.Contains(Path.GetFileName(entry.Path)))));
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
            var occurrenceEnd = occurrence + targetBytes.Value.Length;
            var characterStart = Encoding.UTF8.GetCharCount(sourceFile.RawBytes.AsSpan()[..occurrence]);
            var characterEnd = characterStart + Encoding.UTF8.GetCharCount(targetBytes.Value.AsSpan());
            for (var index = 0; index < leaves.Length; index++)
            {
                if (leaves[index].Start >= characterEnd || leaves[index].End <= characterStart) continue;
                // A stored table header/definition ends where its first body row
                // starts, even when the fresh owner now contains the entire table.
                if (leaves[index] is MarkdownTableRow { IsHeader: false }
                    && leaves[index].Start <= characterStart
                    && MarkdigBlockAst.LineEnd(text, leaves[index].End) >= characterEnd)
                {
                    var first = index;
                    while (first > 0 && leaves[first - 1] is MarkdownTableRow { IsHeader: false }) first--;
                    var rowStart = MarkdownAstAtomizer.ByteOffset(text, leaves[first].Start);
                    var owner = atomized.Claims.FirstOrDefault(atom => atom.StartByte < rowStart && atom.EndByte >= occurrenceEnd);
                    if (owner is not null && owner.StartByte < occurrence)
                        neighborIds.Add(DigestionFingerprint.Compute(sourceFile.RawBytes.AsSpan()[owner.StartByte..rowStart]).RawSha256[7..]);
                }
                for (var neighbor = Math.Max(0, index - 1); neighbor <= Math.Min(leaves.Length - 1, index + 1); neighbor++)
                {
                    // A historical parent owns its interior. Only exterior or crossing
                    // leaves can change its neighbors; stored descendants come from chains.
                    if (leaves[neighbor].Start >= characterStart && leaves[neighbor].End <= characterEnd) continue;
                    var start = MarkdownAstAtomizer.ByteOffset(text, leaves[neighbor].Start);
                    var end = MarkdownAstAtomizer.ByteOffset(text, leaves[neighbor].End);
                    if (start >= occurrence && end <= occurrenceEnd) continue;
                    neighborIds.Add(DigestionFingerprint.Compute(sourceFile.RawBytes.AsSpan()[start..end]).RawSha256[7..]);
                    if (neighbor != index && leaves[neighbor] is MarkdownTableRow)
                    {
                        var lineEnd = MarkdownAstAtomizer.ByteOffset(text, MarkdigBlockAst.LineEnd(text, leaves[neighbor].End));
                        neighborIds.Add(DigestionFingerprint.Compute(sourceFile.RawBytes.AsSpan()[start..lineEnd]).RawSha256[7..]);
                    }
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

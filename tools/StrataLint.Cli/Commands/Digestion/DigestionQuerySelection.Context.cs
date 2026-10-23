using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class DigestionQuerySelection
{
    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadContext(
        IRepositoryGateway repository, string atomId, IReadOnlyList<string>? selectors = null, bool allowMissing = false)
        => ReadContext(repository, atomId, selectors, out _, allowMissing);

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadContext(
        IRepositoryGateway repository, string atomId, IReadOnlyList<string>? selectors,
        out AtomizedTheoryDocument? sourceDocument, bool allowMissing = false)
    {
        sourceDocument = null;
        var loaded = ReadAtom(repository, atomId, selectors);
        var targets = loaded.Document.RequireDigestionEntries().Where(entry => entry.AtomId == atomId).ToArray();
        if (targets.Length != 1) return loaded;
        var target = targets[0];
        loaded = Load(Merge(loaded.Raw, repository.ReadCurrent([
            Literal(DigestionContextPointerIndex.RelativePath(target.SourceId, atomId))])));
        var versions = DigestionContextPointerStore.Load(loaded.Snapshot, target.SourceId, atomId);
        var occurrences = versions.SelectMany(index => index.Entries[0].Occurrences).ToArray();
        var neighborIds = occurrences.SelectMany(occurrence => new[] { occurrence.PreviousAtomId, occurrence.NextAtomId })
            .OfType<string>().Distinct(StringComparer.Ordinal).ToArray();
        var ids = neighborIds.Concat(occurrences.SelectMany(occurrence => occurrence.GoverningContext.Select(scope => scope.AtomId)))
            .Append(atomId).Distinct(StringComparer.Ordinal).ToArray();
        var neighbors = ReadAtoms(repository, neighborIds.Where(id => id != atomId).ToArray());
        var raw = Merge(loaded.Raw, neighbors.Raw);
        var targetPath = loaded.Raw.Entries.Single(entry => IsAtomPath(entry.Path)
            && Path.GetFileNameWithoutExtension(entry.Path) == atomId).Path;
        raw = Merge(raw, repository.ReadCurrent(ids.SelectMany(id => new[] {
            Literal(DigestionCasStore.RootPath + id),
            Literal(DigestionContextPointerIndex.RelativePath(target.SourceId, id)) })
            .Append(Literal(targetPath)).ToArray()));
        return ReadChains(repository, Load(raw), allowMissing: allowMissing);
    }
}

namespace StrataLint.Engine;

// A source is the canonical regular input, never a reader reference or an archive.
internal static class DigestionSourceEligibility
{
    internal static bool IsEligible(RepositorySnapshot snapshot, string path, FileMapManifest? manifest = null)
    {
        if (!snapshot.TryGetFile(path, out _)) return false;
        if (!snapshot.PathInventory.IsDefault
            && snapshot.PathInventory.Any(entry => entry.Path == path
                && (entry.LinkTarget is not null || entry.EffectiveMode is not ("100644" or "100755"))))
            return false;
        if (!snapshot.TryGetFile(FileMapLoader.RelativePath, out _))
            return false;
        return (manifest ?? FileMapLoader.LoadSnapshot(snapshot)).Match(path) is [{ DigestionSource: true, Symlink: null }];
    }

    internal static void Require(RepositorySnapshot snapshot, string path)
    {
        if (!IsEligible(snapshot, path))
            throw new FormatException($"ineligible digestion source: {path}; a canonical eligible regular source is required");
    }
}

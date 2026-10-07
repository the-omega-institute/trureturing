using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class GitRepositoryGateway
{
    public IReadOnlyList<string> SearchCurrentPaths(IReadOnlyList<string> paths)
    {
        var snapshot = GitRepositorySnapshotReader.ReadCurrent(root,
            readContents: static _ => false,
            pathspecs: [.. paths, AdmissionPlanePolicy.FileMapPath, "Meta/FILEMAP.*.toml"]);
        return snapshot.Entries.Select(static entry => entry.Path)
            .Where(static path => !FileMapDocuments.IsPolicyPath(path))
            .Where(path => paths.Any(selection => MatchesPathSelection(path, selection)))
            .ToArray();
    }

    internal static bool MatchesPathSelection(string path, string selection) =>
        selection.StartsWith(":(literal)", StringComparison.Ordinal)
            ? path == selection[10..] || path.StartsWith(selection[10..] + "/", StringComparison.Ordinal)
            : selection.StartsWith(":(glob)", StringComparison.Ordinal)
            ? FileMapGlob.CreateForAdmissionPlane(selection[7..]).IsMatch(path)
            : path == selection || path.StartsWith(selection + "/", StringComparison.Ordinal);
}

using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class CommonExecutionEvidence
{
    // One read-only validation against one snapshot. Never retain this across an
    // execution callback, import copy, or write to any of the inspected paths.
    internal sealed class ValidationScope(RepositorySnapshot snapshot)
    {
        private readonly Dictionary<string, string> hashes = new(StringComparer.Ordinal);
        private readonly HashSet<(string Report, string Archive)> reports = [];
        internal RepositorySnapshot Snapshot { get; } = snapshot;

        internal string Hash(string path)
        {
            path = Path.GetFullPath(path);
            if (!hashes.TryGetValue(path, out var hash))
                hashes.Add(path, hash = CommonExecutionEvidence.Hash(path));
            return hash;
        }

        internal void Report(string path)
        {
            var archive = path + ".materials.zip";
            if (!File.Exists(path) || !File.Exists(archive))
            {
                // Preserve the report reader's diagnostics for missing material.
                _ = RawLeanReportArtifact.ReadFile(path, Snapshot, validateMaterials: true);
                return;
            }
            var identity = (Hash(path), Hash(archive));
            if (reports.Contains(identity)) return;
            _ = RawLeanReportArtifact.ReadFile(path, Snapshot, validateMaterials: true);
            reports.Add(identity);
        }
    }
}

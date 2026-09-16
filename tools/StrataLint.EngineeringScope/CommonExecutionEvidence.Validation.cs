using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class CommonExecutionEvidence
{
    // One read-only validation against one snapshot. Never reuse this across an
    // execution callback, import copy, or write to any of the inspected paths.
    internal sealed class ValidationScope(RepositorySnapshot snapshot)
    {
        private readonly Dictionary<string, string> hashes = new(StringComparer.Ordinal);
        private readonly Dictionary<(string Report, string Archive), LeanAxiomReport> reports = [];
        private IReadOnlyList<RegisteredCommonCheck>? checks;
        internal RepositorySnapshot Snapshot { get; } = snapshot;

        internal static ValidationScope Create(string root) => new(CommonExecutionEvidence.Snapshot(root));

        internal IReadOnlyList<RegisteredCommonCheck> CheckManifest() => CheckManifest(null);

        internal IReadOnlyList<RegisteredCommonCheck> CheckManifest(EngineeringProjectRegistry? registry) =>
            checks ??= ReadCheckManifest(Snapshot, registry);

        internal string Hash(string path)
        {
            path = Path.GetFullPath(path);
            if (!hashes.TryGetValue(path, out var hash))
                hashes.Add(path, hash = CommonExecutionEvidence.Hash(path));
            return hash;
        }

        internal LeanAxiomReport Report(string path)
        {
            var archive = path + ".materials.zip";
            if (!File.Exists(path) || !File.Exists(archive))
            {
                // Preserve the report reader's diagnostics for missing material.
                return RawLeanReportArtifact.ReadFile(path, Snapshot, validateMaterials: true);
            }
            var identity = (Hash(path), Hash(archive));
            if (!reports.TryGetValue(identity, out var report))
                reports.Add(identity, report = RawLeanReportArtifact.ReadFile(path, Snapshot, validateMaterials: true));
            return report;
        }
    }
}

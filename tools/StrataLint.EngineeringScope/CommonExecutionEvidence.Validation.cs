using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class CommonExecutionEvidence
{
    // One read-only validation against one snapshot. Never reuse this across an
    // execution callback, import copy, or write to any of the inspected paths.
    internal sealed class ValidationScope(RepositorySnapshot snapshot, ReportValidation? successfulReport = null)
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
                reports.Add(identity, report = successfulReport is null
                    ? RawLeanReportArtifact.ReadFile(path, Snapshot, validateMaterials: true)
                    : successfulReport.Read(path, Snapshot, identity));
            return report;
        }
    }

    // A CheckExecution may retain one completely validated report across callbacks.
    // Every caller must supply freshly hashed bytes; path hashes stay in its new scope.
    internal sealed class ReportValidation(RepositorySnapshot snapshot)
    {
        private ((string Report, string Archive) Identity, LeanAxiomReport Report)? last;

        internal LeanAxiomReport Read(string path, RepositorySnapshot current, (string Report, string Archive) identity)
        {
            if (!ReferenceEquals(snapshot, current))
                throw new InvalidOperationException("report validation belongs to another snapshot");
            if (last is { } accepted && accepted.Identity == identity) return accepted.Report;
            var report = RawLeanReportArtifact.ReadFile(path, current, validateMaterials: true);
            // Publish only after all source bindings and ZIP statement materials passed.
            // The reader retains its archive bytes in memory, independent of this path.
            last = (identity, report);
            return report;
        }
    }
}

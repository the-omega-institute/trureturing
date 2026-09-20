using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class CommonExecutionEvidence
{
    // One read-only validation against one snapshot. Hashes never cross an
    // execution callback, import copy, or write to any of the inspected paths.
    internal sealed class ValidationScope(RepositorySnapshot snapshot, ReportValidation? successfulReport = null)
    {
        private readonly Dictionary<string, string> hashes = new(StringComparer.Ordinal);
        private readonly Dictionary<(string Report, string Archive), LeanAxiomReport> reports = [];
        private IReadOnlyList<RegisteredCommonCheck>? checks;
        internal RepositorySnapshot Snapshot { get; } = snapshot;

        internal static ValidationScope Create(string root) => new(CommonExecutionEvidence.Snapshot(root));

        // Only successful registration from this exact snapshot is shared. No caller
        // can supply declarations or inherit path hashes from an earlier phase.
        internal ValidationScope Fresh(ReportValidation? report = null) => new(Snapshot, report) { checks = checks };

        internal IReadOnlyList<RegisteredCommonCheck> CheckManifest() => CheckManifest(null);

        internal IReadOnlyList<RegisteredCommonCheck> CheckManifest(EngineeringProjectRegistry? registry) =>
            (checks ??= ReadCheckManifest(Snapshot, registry)).Select(check => check with
            {
                ProgramProjects = [.. check.ProgramProjects],
                Materials = [.. check.Materials],
                MaterialExcludes = [.. check.MaterialExcludes],
                PathInventory = [.. check.PathInventory],
                ReportInputs = check.ReportInputs.Select(input => input with { Materials = [.. input.Materials] }).ToArray(),
                DeltaScope = check.DeltaScope is not { } scope ? null : new([.. scope.WholeTreeInputs], [.. scope.ActorInputs],
                    scope.Related.Select(row => new RegisteredFileMapRelatedScope([.. row.Inputs], [.. row.Paths])).ToArray(), [.. scope.InventoryInputs!]),
                MarkdownScope = check.MarkdownScope is not { } markdown ? null : new([.. markdown.WholeTreeInputs], [.. markdown.ChangedInputs]),
            }).ToArray();

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

    // One CheckExecution or seed import may retain a completely validated report.
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

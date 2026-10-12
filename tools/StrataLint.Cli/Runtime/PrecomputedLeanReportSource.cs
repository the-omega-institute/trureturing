using StrataLint.Runtime;
using StrataLint.Engine;
using System.Text;

namespace StrataLint.Cli;

internal sealed class PrecomputedLeanReportSource(string repositoryRoot) : ILeanReportSource
{
    private readonly string reportPath = LeanCompiledArtifactReports.ResolveReportPath(repositoryRoot);

    public LeanAxiomReport Load(RepositorySnapshot snapshot) =>
        RawLeanReportArtifact.ReadFile(reportPath, snapshot);

    public LeanAxiomReport Load(LeanReportScope scope) =>
        RawLeanReportArtifact.ReadFileForScope(reportPath, scope, validateMaterials: true);

    internal CapturedBundle Capture() => new(repositoryRoot, reportPath);

    internal sealed class CapturedBundle(string repositoryRoot, string sourcePath) : ILeanReportSource, IDisposable
    {
        private static readonly string[] Suffixes = ["", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip"];
        private readonly string directory = Path.Combine(Path.GetTempPath(), "stratalint-report-consumer-" + Guid.NewGuid().ToString("N"));
        private string ReportPath => Path.Combine(directory, Path.GetFileName(sourcePath));
        private string? targets;

        public LeanAxiomReport Load(RepositorySnapshot snapshot)
        {
            CaptureFiles();
            return RawLeanReportArtifact.ReadFile(ReportPath, snapshot);
        }

        public LeanAxiomReport Load(LeanReportScope scope)
        {
            CaptureFiles();
            targets = string.Join(' ', scope.Targets.Select(static path => path.Value[..^5].Replace('/', '.')));
            return RawLeanReportArtifact.ReadFileForScope(ReportPath, scope, validateMaterials: true);
        }

        private void CaptureFiles()
        {
            Directory.CreateDirectory(directory);
            // Keep the report and its lazy statement materials alive for the entire batch.
            // Missing companions retain the final emission's failure-after-commit behavior.
            foreach (var suffix in Suffixes)
                if (File.Exists(sourcePath + suffix))
                    File.Copy(sourcePath + suffix, ReportPath + suffix);
        }

        internal void ValidateForEmission()
        {
            if (string.IsNullOrWhiteSpace(targets))
                throw new InvalidOperationException("captured report has no explicit Lean target scope");
            foreach (var suffix in Suffixes)
                if (!File.Exists(ReportPath + suffix))
                    throw new InvalidOperationException("raw Lean report bundle is incomplete at " + sourcePath + suffix);
            var verification = BoundedProcessRunner.Run("/bin/bash",
                [Path.Combine(repositoryRoot, "tools/scripts/report/lean-report-input.sh"), "verify-scoped",
                    "--repository", repositoryRoot, "--report", ReportPath, "--targets", targets],
                repositoryRoot, BoundedProcessRunner.HangDetectionBudget, 64 * 1024 * 1024);
            if (verification.ExitCode != 0)
                throw new InvalidOperationException(Encoding.UTF8.GetString(verification.StandardError).Trim());
        }

        public void Dispose()
        {
            if (Directory.Exists(directory)) Directory.Delete(directory, recursive: true);
        }
    }
}

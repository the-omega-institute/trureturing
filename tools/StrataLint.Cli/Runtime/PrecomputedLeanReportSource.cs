using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class PrecomputedLeanReportSource(string repositoryRoot) : ILeanReportSource
{
    private readonly string reportPath = LeanCompiledArtifactReports.ResolveReportPath(repositoryRoot);

    public LeanAxiomReport Load(RepositorySnapshot snapshot) =>
        RawLeanReportArtifact.ReadFile(reportPath, snapshot);
}
